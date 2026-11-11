-- Prove2me | Definitions.Def_SingleExpBisect_Main_Encodings
-- name    : SingleExpBisect_Main_Encodings
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T17:40:38.106813+00:00
-- url     : https://prove2.me/theorems/b1faeb0e-8f26-4c9f-ab3d-a63d2590a149
-- title:
--   Step bound C·2^{Ck}·(n+1)^C and bit encodings of families, monomials, sparse polynomials and node inputs
-- statement:
--   Algorithms are deterministic multi-stack Turing machines with Boolean alphabets (published `HMBinPacking.OutputsWithin`); numbers use the published self-delimiting binary code `encodeNat` / `encodeRat`, graphs the published `encodeInput G k`, vertex sets `encodeSet`, decompositions `encodeTD`.
--
--   - `stepBound C k n` $=C\cdot2^{C k}\cdot(n+1)^C$: the paper's $O^*(2^{O(k)})$ with one constant $C$.
--   - `encodeFamily L`: a list of vertex sets (length, then each set).
--   - `encodeExp e`, `encodeTerms L`: a monomial by its exponents of $x,x',w,y_0,\dots,y_{n-1}$; a list of (monomial, rational coefficient) pairs.
--   - `IsSparseRep L f`: the monomials of $L$ are distinct, every listed coefficient is nonzero, and $f(e)$ is the coefficient listed for $e$ (zero if unlisted): $L$ lists exactly the nonzero coefficients of $f$.
--   - `nodeInput G k T t`: the graph, $k$, the decomposition and the node $t$; `childInput T t Lc`: for each child $s$ of $t$ in increasing order, $s$ and the term list `Lc s`.
-- source:
--   Kumabe, Single-Exponential FPT Algorithms for Minimum Bisection and Matching Cut via a New Unbreakable Decomposition, arXiv:2611.05982 (October 2026 version; PDF SHA256 6530ce94…6b76541), footnote 1, p. 3 (O*); §3.1, p. 16 and §3.3, pp. 20–23 (the polynomials passed between nodes)

import Mathlib
import Definitions.Def_MinBisectFPT_encodeCounts
import Definitions.Def_MinBisectFPT_encodeTD
import Definitions.Def_SingleExpBisect_Main_NodeData

open scoped Classical

namespace SingleExpBisect.Main

open MinBisectFPT ExponomialAssortment.FPTAS

/-- **The step bound `O*(2^{O(k)})`.** Kumabe, *Single-Exponential FPT Algorithms for Minimum
Bisection and Matching Cut via a New Unbreakable Decomposition*, arXiv:2611.05982 (October 2026),
footnote 1, p. 3: "The O∗ notation suppresses factors polynomial in the input size." With one
constant `C`: `C · 2^{C·k} · (n + 1)^C`, where `n = |V(G)|` (`n + 1` keeps the bound positive at
`n = 0`). -/
def stepBound (C k n : ℕ) : ℕ := C * 2 ^ (C * k) * (n + 1) ^ C

/-- A list of vertex sets (an enumerated family): its length, then each set with the published
`encodeSet`. Order and repetitions are the algorithm's choice. -/
noncomputable def encodeFamily {n : ℕ} (L : List (Finset (Fin n))) : List Bool :=
  encodeNat L.length ++ L.flatMap encodeSet

/-- A monomial `x^{e_x} x′^{e_{x′}} w^{e_w} Π_v y_v^{e_{y_v}}`: its exponents of `x`, `x′`, `w`,
then of `y_0, …, y_{n−1}`, all with the published integer code. -/
noncomputable def encodeExp {n : ℕ} (e : Var n →₀ ℕ) : List Bool :=
  encodeNat (e Var.x) ++ encodeNat (e Var.x') ++ encodeNat (e Var.w) ++
    (List.finRange n).flatMap (fun v => encodeNat (e (Var.y v)))

/-- A list of terms (monomial, rational coefficient): its length, then each monomial with
`encodeExp` and its coefficient with the published `encodeRat`. -/
noncomputable def encodeTerms {n : ℕ} (L : List ((Var n →₀ ℕ) × ℚ)) : List Bool :=
  encodeNat L.length ++ L.flatMap (fun p => encodeExp p.1 ++ encodeRat p.2)

/-- **`L` lists the nonzero coefficients of the coefficient function `f`**: the monomials of `L`
are distinct, every listed coefficient is nonzero, and the coefficient of every monomial `e` is the
one listed for `e` (zero if `e` is not listed). So `f` has finite support and `L` is its sparse
representation, up to order. -/
def IsSparseRep {n : ℕ} (L : List ((Var n →₀ ℕ) × ℚ)) (f : (Var n →₀ ℕ) → ℚ) : Prop :=
  (L.map Prod.fst).Nodup ∧ (∀ p ∈ L, p.2 ≠ 0) ∧
    ∀ e, f e = ((L.filter (fun p => decide (p.1 = e))).map Prod.snd).sum

/-- **Input naming a node of a decomposition**: the published `encodeInput G k`, the published
`encodeTD T`, then the node `t`. -/
noncomputable def nodeInput {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) (T : RootedTD n)
    (t : Fin T.N) : List Bool :=
  encodeInput G k ++ encodeTD T ++ encodeNat t.val

/-- **The children's polynomials as input.** For each child `s` of `t`, in increasing order of `s`:
the index `s`, then the term list `Lc s` (which the theorems require to be the sparse
representation of `Z_s(ω^{∂G_s}_s(y, x), w)`). -/
noncomputable def childInput {n : ℕ} (T : RootedTD n) (t : Fin T.N)
    (Lc : Fin T.N → List ((Var n →₀ ℕ) × ℚ)) : List Bool :=
  ((List.finRange T.N).filter (fun s => decide (T.parent s = some t))).flatMap
    (fun s => encodeNat s.val ++ encodeTerms (Lc s))

end SingleExpBisect.Main


