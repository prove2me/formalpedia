-- Prove2me | Definitions.Def_CopylessCRA_Supplement_IsUnipotentSeries
-- name    : CopylessCRA_Supplement_IsUnipotentSeries
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T02:57:03.310203+00:00
-- url     : https://prove2.me/theorems/71bd4510-a423-4367-95e2-81c4f9fe5cff
-- title:
--   Unipotent and quasi-unipotent rational series and the two sector normal forms
-- statement:
--   This module supplies the objects in Theorem 2.
--
--   A rational series is **unipotent** when every word matrix $M_w$ in a minimal representation is unipotent, equivalently every eigenvalue is $1$. It is **quasi-unipotent** when every eigenvalue of every $M_w$ is a root of unity. Both definitions quantify over all words, not just letters.
--
--   It also defines permutation invariance, letter counts $|w|_a$, rational-polynomial dependence on those counts, virtual abelianness of the generated letter group, and pairwise commutation of the unipotent word matrices. For a morphism $\varphi:\Sigma^*\to F$ to a finite group, $|w|_{h,a}$ counts positions carrying $a$ for which the group state before that position is $h$; the finite-group normal form is
--
--   $$
--   f(w)=P_{\varphi(w)}\big((|w|_{h,a})_{h\in F,a\in\Sigma}\big).
--   $$
--
--   **Formalization Note** Roots of unity are roots of characteristic polynomials after scalar extension to $\overline{\mathbb Q}$; this permits nontrivial Jordan blocks. Finite groups and word morphisms are bundled only to carry their operations and finiteness data.
-- source:
--   Zeng–Cao–Dai–Wang–Ding, Copyless Cost Register Automata and Algebraic Groups, STOC 2027 submission (manuscript sha256 434d3094df2665371c402d5b5291b3c7f3a27a0d79384e4a8ec3ca3a46a92543), paragraph before Theorem 2 and Theorem 2, p.3 (PDF p.5); proof, p.13 (PDF p.15)

import Mathlib
import Definitions.Def_CopylessCRA_CCRA
import Definitions.Def_CopylessCRA_IsRep
import Definitions.Def_CopylessCRA_zariskiClosure

open Matrix

namespace CopylessCRA
namespace Supplement

/-- A rational series is **unipotent** when every word matrix in a minimal representation is
unipotent, i.e. every eigenvalue is `1`.  Zeng--Cao--Dai--Wang--Ding, *Copyless Cost Register
Automata and Algebraic Groups*, STOC 2027 submission (manuscript sha256 434d3094...),
Theorem 2 and the paragraph preceding it, p.3 (PDF p.5).

**Formalization Note** The predicate is attached to the supplied minimal representation.  Theorem 2
also assumes that this representation represents `f` and is minimal, so uniqueness up to conjugacy
makes the predicate intrinsic to `f`.  The quantifier is over all words, including the empty word,
not only over letters. -/
def IsUnipotentSeries {alpha iota : Type*} [Fintype iota] [DecidableEq iota]
    (M : alpha -> Matrix iota iota ℚ) : Prop :=
  forall w : List alpha, IsUnipotent (wordMat M w)

/-- A rational series is **quasi-unipotent** when every eigenvalue of every word matrix in a
minimal representation is a root of unity (Theorem 2, p.3, PDF p.5).

**Formalization Note** Eigenvalues are expressed as roots of the characteristic polynomial after
extension from `ℚ` to its algebraic closure.  A root of unity may occur in a nontrivial Jordan
block; the definition therefore does not incorrectly require a power of the whole matrix to be
the identity. -/
def IsQuasiUnipotentSeries {alpha iota : Type*} [Fintype iota] [DecidableEq iota]
    (M : alpha -> Matrix iota iota ℚ) : Prop :=
  forall (w : List alpha) (mu : Qbar),
    Polynomial.IsRoot ((wordMat M w).charpoly.map (algebraMap ℚ Qbar)) mu ->
      exists n : ℕ, 0 < n ∧ mu ^ n = 1

/-- Invariance under arbitrary permutations of the input positions. -/
def IsPermutationInvariant {alpha : Type*} (f : List alpha -> ℚ) : Prop :=
  forall u v, u.Perm v -> f u = f v

/-- The number `|w|_a` of occurrences of the letter `a` in `w`. -/
def letterCount {alpha : Type*} [DecidableEq alpha] (w : List alpha) (a : alpha) : ℕ :=
  w.count a

/-- `f(w)` is a rational polynomial in the letter counts `(|w|_a)_a`. -/
def HasLetterCountPolynomial {alpha : Type*} [DecidableEq alpha]
    (f : List alpha -> ℚ) : Prop :=
  exists P : MvPolynomial alpha ℚ, forall w,
    f w = MvPolynomial.eval (fun a => (letterCount w a : ℚ)) P

/-- A bundled finite group used for the finite-control normal form in Theorem 2(2). -/
structure FiniteGroupModel where
  Carrier : Type
  group : Group Carrier
  fintype : Fintype Carrier
  decidableEq : DecidableEq Carrier

instance (G : FiniteGroupModel) : Group G.Carrier := G.group
instance (G : FiniteGroupModel) : Fintype G.Carrier := G.fintype
instance (G : FiniteGroupModel) : DecidableEq G.Carrier := G.decidableEq

/-- A monoid morphism from words under concatenation to a finite group. -/
structure WordMorphism (alpha : Type*) (G : FiniteGroupModel) where
  toFun : List alpha -> G.Carrier
  map_nil : toFun [] = 1
  map_append : forall u v, toFun (u ++ v) = toFun u * toFun v

instance {alpha : Type*} {G : FiniteGroupModel} : CoeFun (WordMorphism alpha G)
    (fun _ => List alpha -> G.Carrier) := ⟨WordMorphism.toFun⟩

/-- The transition count `|w|_{h,a}`: the number of positions carrying `a` at which the finite-group
state *before* reading that position is `h`. -/
def transitionCount {alpha : Type*} [DecidableEq alpha] (G : FiniteGroupModel)
    (phi : WordMorphism alpha G) (w : List alpha) (h : G.Carrier) (a : alpha) : ℕ :=
  let rec go (q : G.Carrier) : List alpha -> ℕ
    | [] => 0
    | b :: rest => (if q = h ∧ b = a then 1 else 0) + go (q * phi [b]) rest
  go 1 w

/-- The finite-group transition-count normal form in Theorem 2(2): a finite group `F`, a monoid
morphism `phi : Sigma* -> F`, and one rational polynomial `P_g` in the variables `n_{h,a}` for
each final group element `g`, with `f(w) = P_{phi(w)}((|w|_{h,a})_{h,a})`. -/
def HasTransitionCountNormalForm {alpha : Type*} [DecidableEq alpha]
    (f : List alpha -> ℚ) : Prop :=
  exists G : FiniteGroupModel, exists phi : WordMorphism alpha G,
    exists P : G.Carrier -> MvPolynomial (G.Carrier × alpha) ℚ, forall w,
      f w = MvPolynomial.eval
        (fun ha => (transitionCount G phi w ha.1 ha.2 : ℚ)) (P (phi w))

/-- The group generated by the minimal letter matrices is virtually abelian. -/
def IsLetterGroupVirtuallyAbelian {alpha iota : Type*} [Fintype iota] [DecidableEq iota]
    (M : alpha -> Matrix iota iota ℚ) : Prop :=
  exists H : Subgroup (Matrix iota iota ℚ)ˣ, H ≤ letterGroup M ∧
    (H.subgroupOf (letterGroup M)).FiniteIndex ∧
    forall g, g ∈ H -> forall h, h ∈ H -> Commute g h

/-- Pairwise commutation of those word matrices that are unipotent. -/
def UnipotentWordMatricesCommute {alpha iota : Type*} [Fintype iota] [DecidableEq iota]
    (M : alpha -> Matrix iota iota ℚ) : Prop :=
  forall x y : List alpha, IsUnipotent (wordMat M x) -> IsUnipotent (wordMat M y) ->
    Commute (wordMat M x) (wordMat M y)

end Supplement
end CopylessCRA


