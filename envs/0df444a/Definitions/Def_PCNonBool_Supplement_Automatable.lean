-- Prove2me | Definitions.Def_PCNonBool_Supplement_Automatable
-- name    : PCNonBool_Supplement_Automatable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:27:46.406475+00:00
-- url     : https://prove2.me/theorems/41782044-456c-47e7-a823-65a0de170f9a
-- title:
--   Automatability of $\mathcal P$ and polynomial-time SAT
-- statement:
--   A proof system is **automatable in polynomial time** [BPR00] if an algorithm takes any unsatisfiable CNF formula $G$ and outputs a refutation of $G$ in time polynomial in $S(G)+\mathrm{size}(G)$, where $S(G)$ is the size of the smallest refutation of $G$.
--
--   For $\mathcal P$ over a field $\mathbb F$ this is stated with a Mathlib two-stack Turing machine and a polynomial $q$: on the encoding of every unsatisfiable $G$ the machine halts within $q(S(G)+|\mathrm{enc}(G)|)$ steps and outputs the monomial structure (lines, their monomials, and the variables of each monomial) of some $\mathcal P$-refutation of $G$. Alongside, **SAT is in polynomial time** means that a two-stack Turing machine decides satisfiability of CNF formulas in time polynomial in the length of their encoding; by the Cook–Levin theorem this is equivalent to $\mathrm P=\mathrm{NP}$.
--
--   These are the hypothesis and the conclusion of the "in particular" part of Theorem 7.1.
--
--   **Formalization Note** Elements of an arbitrary field have no finite encoding, so the machine outputs only the monomials of the lines, and suitable coefficients are required to exist. This is a weaker hypothesis than outputting the refutation itself, so the implication stated with it is at least as strong as the paper's.
-- source:
--   Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, On the Power of Polynomial Calculus over Non-Boolean Domains, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), §7, p.50 (PDF p.53); proof of Theorem 7.1, p.52 (PDF p.55)

import Mathlib
import Definitions.Def_PCNonBool_IsRefutation
import Definitions.Def_PCNonBool_pcSize
import Definitions.Def_PCNonBool_Supplement_CNF
import Definitions.Def_PCNonBool_Supplement_encodeCNF
import Definitions.Def_PCNonBool_Supplement_ProofSystemP

namespace PCNonBool.Supplement

/-- The minimum size `S(G)` of a `P`-refutation of the CNF formula `G` over `F` (`0` if there is
none) (Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), §7, p.50 (PDF p.53)). -/
noncomputable def minPSize (F : Type*) [Field F] (G : CNF) : ℕ :=
  sInf {s | ∃ π : List (MvPolynomial PVar F), PCNonBool.IsRefutation redP (PAxioms F G) π ∧
    PCNonBool.pcSize π = s}

/-- The output format of an automating algorithm: a list of lines, each line the list of its
monomials, each monomial the list of the `P`-variables in it (reduced monomials are multilinear). -/
abbrev RefShape : Type := List (List (List PVar))

/-- The encoding of a `RefShape`: each variable `(v, t)` as a kind mark, the binary code of `v`
and `sep`; each monomial closed by `endM`, each line by `endL`. -/
def encodeShape (r : RefShape) : List Sym :=
  r.flatMap fun line => line.flatMap (fun mono => mono.flatMap (fun x =>
    (match x.2 with
      | 0 => Sym.kw
      | 1 => Sym.kbar
      | 2 => Sym.kfour) :: (encNat x.1 ++ [Sym.sep])) ++ [Sym.endM]) ++ [Sym.endL]

/-- `r` is the monomial structure of a `P`-refutation of `G` over `F`: there is a `P`-refutation
with one line per entry of `r` whose `k`-th line has exactly the monomials listed in `r[k]`. -/
def IsShapeOfPRefutation (F : Type*) [Field F] (G : CNF) (r : RefShape) : Prop :=
  ∃ π : List (MvPolynomial PVar F), PCNonBool.IsRefutation redP (PAxioms F G) π ∧
    ∃ h : π.length = r.length, ∀ (k : ℕ) (hk : k < π.length),
      (π[k]).support = ((r[k]'(h ▸ hk)).map fun mono => Multiset.toFinsupp (mono : Multiset PVar)).toFinset

/-- `P` over `F` is **automatable in polynomial time** [BPR00] (Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), §7, p.50 (PDF p.53)): "there
is an algorithm that takes as input an unsatisfiable CNF formula `F` and outputs a `P`-refutation
of `F` in time polynomial in the size of the smallest `P`-refutation of `F` plus the size of `F`".
Here: a Mathlib two-stack Turing machine `tm` and a polynomial `q` such that on (the encoding of)
every unsatisfiable `G` it halts within `q(S(G) + |enc G|)` steps with (the encoding of) the
monomial structure of a `P`-refutation of `G`.

**Formalization Note** Field elements of an arbitrary field have no finite encoding, so the
machine outputs the lines' monomials and the coefficients are only required to exist. This makes
"automatable" a weaker hypothesis than outputting the refutation with its coefficients, so every
implication "automatable → …" is at least as strong as with the paper's notion. -/
def IsAutomatable (F : Type) [Field F] : Prop :=
  ∃ (tm : Turing.FinTM2) (inA : tm.Γ tm.k₀ ≃ Sym) (outA : tm.Γ tm.k₁ ≃ Sym) (q : Polynomial ℕ),
    ∀ G : CNF, ¬ Satisfiable G → ∃ r : RefShape, IsShapeOfPRefutation F G r ∧
      Nonempty (Turing.TM2OutputsInTime tm ((encodeCNF G).map inA.symm)
        (some ((encodeShape r).map outA.symm)) (q.eval (minPSize F G + (encodeCNF G).length)))

/-- CNF satisfiability is decidable in polynomial time by a Mathlib two-stack Turing machine on the
encoding `encodeCNF`. By the Cook–Levin theorem this is equivalent to `P = NP`; it is the form in
which the paper derives `P = NP` ("3-SAT can be decided …", p.52 (PDF p.55)). -/
def SATinP : Prop :=
  open Classical in
  Nonempty (Turing.TM2ComputableInPolyTime encodeCNF Computability.encodeBool
    (fun G : CNF => decide (Satisfiable G)))

end PCNonBool.Supplement


