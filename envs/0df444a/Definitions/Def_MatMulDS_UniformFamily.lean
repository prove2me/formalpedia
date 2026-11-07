-- Prove2me | Definitions.Def_MatMulDS_UniformFamily
-- name    : MatMulDS_UniformFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:02:47.444858+00:00
-- url     : https://prove2.me/theorems/3a5e7428-d3ba-41c4-81ac-ccdd2a5955d5
-- title:
--   Uniform families of bilinear data structures
-- statement:
--   A family of bilinear data structures is **uniform** if one program on the published algebraic RAM with no coin instruction, one list of constants and one constant $K$ generate it, for every word size above a threshold:
--
--   1. the preprocessing part, from the parameter words alone, halts within $K(T_{\mathrm{pre}}+1)$ steps and stores the code of $\Phi,\Psi,a,b,C_{\mathrm{box}}$;
--   2. the query part, from that stored structure and a query $(I,J)$, halts within $K(s+1)$ steps with the code of the circuits of that query, where $s$ is their size.
--
--   This makes precise the source's "if a circuit has size $s$ we can construct it in $O(s)$ time". The relation **`AdmitsDS`** says that arbitrary $A,B$ with $(N,D)$ in a range admit a uniform family, generated from the words $N,D$, with given bounds on $T_{\mathrm{pre}}$ and $T_{\mathrm{query}}$.
--
--   **Formalization Note** The query circuits are constructed from what the preprocessing part stored, as in the source, where the labelings are computed "in an initial preprocessing step" and the query circuits after it. The stored structure depends only on the parameters.
-- source:
--   J. Alman, J. Nogler, V. Vassilevska Williams, Subquadratic Time Matrix Multiplication Data Structures Beyond the Dual Exponent, with Applications, STOC 2027 submission (held file sha256 6c5a1c16…), §4.1, p.15 (PDF p.17); §4.2, p.16 (PDF p.18)

import Mathlib
import Definitions.Def_MatMulDS_BilinearDS
import Definitions.Def_MatMulDS_IsMatMulOracle

set_option autoImplicit false

open MatroidSensOracle

namespace MatMulDS

variable {F : Type} [Field F]

/-- The word part of the code of a gate: an opcode and two arguments. -/
def LinGate.codeWords : LinGate F → List ℤ
  | .input i => [0, (i : ℤ), 0]
  | .scale _ g => [1, (g : ℤ), 0]
  | .add g h => [2, (g : ℤ), (h : ℤ)]

/-- The field part of the code of a gate: its scalar, or `0`. -/
def LinGate.codeField : LinGate F → F
  | .scale c _ => c
  | _ => 0

/-- The word part of the code of a circuit: its numbers of gates and outputs, its gates, its outputs. -/
def LinCircuit.codeWords (C : LinCircuit F) : List ℤ :=
  [(C.gates.length : ℤ), (C.outputs.length : ℤ)] ++ C.gates.flatMap LinGate.codeWords ++
    C.outputs.map fun o => (o : ℤ)

/-- The field part of the code of a circuit: the scalars of its gates. -/
def LinCircuit.codeFields (C : LinCircuit F) : List F := C.gates.map LinGate.codeField

namespace BilinearDS

variable {N D : ℕ} (S : BilinearDS F N D)

/-- The word part of the code of the preprocessing circuits `Φ`, `Ψ`, `a`, `b`, `Cbox`. -/
def prepWords : List ℤ :=
  S.Φ.codeWords ++ S.Ψ.codeWords ++ [(S.Ppre : ℤ)] ++
    ((List.finRange S.Ppre).map fun p => (S.a p : ℤ)) ++
    ((List.finRange S.Ppre).map fun p => (S.b p : ℤ)) ++ S.Cbox.codeWords

/-- The field part of the code of the preprocessing circuits. -/
def prepFields : List F := S.Φ.codeFields ++ S.Ψ.codeFields ++ S.Cbox.codeFields

/-- The word part of the code of the circuits of the query `(I, J)`. -/
def queryCodeWords (I J : Fin N) : List ℤ :=
  (S.CAnew I J).codeWords ++ (S.CBnew I J).codeWords ++ [((S.Crel I J).length : ℤ)] ++
    (S.Crel I J).map fun t => (t.2 : ℤ)

/-- The field part of the code of the circuits of the query `(I, J)`. -/
def queryCodeFields (I J : Fin N) : List F :=
  (S.CAnew I J).codeFields ++ (S.CBnew I J).codeFields ++ (S.Crel I J).map Prod.fst

end BilinearDS

/-- The words `ws` lie from word cell `wb` on and the field elements `fs` from field cell `0` on. -/
def MemHolds {w : ℕ} (st : (ℤ → BitVec w) × (ℤ → F)) (wb : ℤ) (ws : List ℤ) (fs : List F) : Prop :=
  (∀ k : ℕ, k < ws.length → (st.1 (wb + k)).toInt = ws.getD k 0) ∧
  (∀ k : ℕ, k < fs.length → st.2 k = fs.getD k 0)

variable [DecidableEq F]

/-- **A generator of a family of bilinear data structures.** `O` is a coin-free program on the published
algebraic RAM with the fixed list of constants `c`, working for every word size `w ≥ K · bits x + K`.
* Its preprocessing part, from the words `words x` alone (not from any matrix), halts within
  `K (Tpre + 1)` steps, stores at most `K (Tpre + 1)` cells, and its stored structure holds the code of
  `Φ`, `Ψ`, `a`, `b`, `Cbox`, in word cells `2, 3, …` and field cells `0, 1, …`.
* Its query part, from that stored structure and the query `(I, J)`, halts within `K (s + 1)` steps, where
  `s` is the size of the circuits of that query, with their code from word cell `0` and field cell `0` on.

Source: STOC 2027 submission (held file sha256 6c5a1c16…), §4.1, p.15: "All circuits are uniform, in the
sense that if a circuit has size s we can construct it in O(s) time"; §4.2, p.16: "we assume Dthin is really
a family of data structures".

**Formalization Note.**
* A single finite circuit has no `O(s)`, so uniformity is a property of a family, with one program and one
  constant `K`.
* The query circuits are constructed at query time from what the preprocessing part stored, not from the
  words alone. This is how the paper constructs them: Lemma A.4 computes the labelings "in an initial
  preprocessing step" (p.71) and Theorem A.7(i) then constructs the query circuits in `Õ(D0^Q)` time (p.77). A
  from-scratch reading would have to redo that labeling at each query, which the paper does not do. The
  stored structure still depends only on `words x`.
* The circuits may be padded with useless gates to reach `O(s)`; the bounds of the theorems count them. -/
structure IsUniformGen (O : AOracle) (c : List F) (K : ℕ) {ι : Type} (N D : ι → ℕ)
    (ds : ∀ x, BilinearDS F (N x) (D x)) (words : ι → List ℤ) (bits : ι → ℕ) : Prop where
  no_coin_prep : ∀ i ∈ O.prep, ¬ i.IsCoin
  no_coin_query : ∀ i ∈ O.query, ¬ i.IsCoin
  runs : ∀ (x : ι) (w : ℕ), K * bits x + K ≤ w →
    ∃ st : (ℤ → BitVec w) × (ℤ → F),
      aexec O.prep (fun _ => 0) (K * ((ds x).Tpre + 1)) 0 0 (aloadWords w (words x)) (aloadFields c) =
        some st ∧
      (st.1 0).toNat + (st.1 1).toNat ≤ K * ((ds x).Tpre + 1) ∧
      (ds x).prepWords.length ≤ (st.1 0).toNat ∧
      (ds x).prepFields.length ≤ (st.1 1).toNat ∧
      MemHolds st 2 (ds x).prepWords (ds x).prepFields ∧
      ∀ I J : Fin (N x),
        ∃ r : (ℤ → BitVec w) × (ℤ → F),
          aexec O.query (fun _ => 0) (K * ((ds x).querySize I J + 1)) 0 0
            (aQueryMemory st (queryWords I J) []).1 (aQueryMemory st (queryWords I J) []).2 = some r ∧
          MemHolds r 0 ((ds x).queryCodeWords I J) ((ds x).queryCodeFields I J)

/-- A family of bilinear data structures is **uniform** if some program generates it. -/
def UniformFamily {ι : Type} (N D : ι → ℕ) (ds : ∀ x, BilinearDS F (N x) (D x)) (words : ι → List ℤ)
    (bits : ι → ℕ) : Prop :=
  ∃ (O : AOracle) (c : List F) (K : ℕ), IsUniformGen O c K N D ds words bits

/-- **Arbitrary `A ∈ F^{N×D}`, `B ∈ F^{D×N}` admit a bilinear data structure** with preprocessing time
`TP N D` and query time `TQ N D`, for all `(N, D)` in the range `X`: a uniform family `ds`, generated from the
words `N, D` with word size above `K⌈log₂(N+1)⌉ + K`, and with those bounds.
Source: STOC 2027 submission (held file sha256 6c5a1c16…), Definition 4.1, pp.15–16; Proposition A.10(iii),
p.80; Corollary 7.2, p.45; Theorem 7.3, p.46.

**Formalization Note** The space of the data structure obtained by evaluating the circuits is at most its
preprocessing time, and its queries may be adaptive since the circuits of a query depend only on that query
(§4.1, p.16; proof of Theorem 7.3, p.46). So these two words of the paper need no separate clause. -/
def AdmitsDS (F : Type) [Field F] [DecidableEq F] (X : ℕ → ℕ → Prop) (TP TQ : ℕ → ℕ → ℝ) : Prop :=
  ∃ ds : ∀ x : {x : ℕ × ℕ // X x.1 x.2}, BilinearDS F x.1.1 x.1.2,
    UniformFamily (fun x : {x : ℕ × ℕ // X x.1 x.2} => x.1.1) (fun x => x.1.2) ds
      (fun x => inputWords x.1.1 x.1.2) (fun x => Nat.clog 2 (x.1.1 + 1)) ∧
    ∀ x : {x : ℕ × ℕ // X x.1 x.2},
      ((ds x).Tpre : ℝ) ≤ TP x.1.1 x.1.2 ∧ ((ds x).Tquery : ℝ) ≤ TQ x.1.1 x.1.2

end MatMulDS


