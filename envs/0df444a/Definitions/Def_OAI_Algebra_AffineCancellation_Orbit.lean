-- Prove2me | Definitions.Def_OAI_Algebra_AffineCancellation_Orbit
-- name    : OAI_Algebra_AffineCancellation_Orbit
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T17:53:29.922419+00:00
-- url     : https://prove2.me/theorems/74203018-c091-46a5-af04-33fd3687d70e
-- title:
--   Exponential orbit polynomial $\sum_n D^n(r)\,T^n/n!$ of a locally nilpotent derivation
-- statement:
--   Let $k$ be a field, $R$ a commutative $k$-algebra and $D$ a $k$-linear derivation of $R$. Write $D^n$ for the $n$-fold iterate of $D$, with $D^0=\mathrm{id}$.
--
--   1. **Local nilpotence.** $D$ is locally nilpotent if for every $r\in R$ there is $n\ge0$ with $D^n(r)=0$.
--
--   2. **Higher Leibniz rule.** For all $n\ge0$ and $r,s\in R$,
--   $$D^n(rs)=\sum_{i+j=n}\binom{n}{i}\,D^i(r)\,D^j(s).$$
--
--   3. **Orbit polynomial.** For a locally nilpotent $D$ and $r\in R$,
--   $$\mathrm{orb}_D(r)=\sum_{n\ge0}\frac{1}{n!}\,D^n(r)\,T^n\in R[T].$$
--   Only finitely many terms are nonzero, so this is a polynomial. Its constant coefficient is $r$ and its linear coefficient is $D(r)$. Moreover $\mathrm{orb}_D(r+s)=\mathrm{orb}_D(r)+\mathrm{orb}_D(s)$, and every scalar $a\in k$ (that is, its image in $R$) is sent to the constant polynomial $a$.
--
--   4. **Exponential homomorphism.** If $k$ has characteristic zero, then $\frac{1}{n!}\binom{n}{i}=\frac{1}{i!\,j!}$ whenever $i+j=n$. In that case $\mathrm{orb}_D(rs)=\mathrm{orb}_D(r)\,\mathrm{orb}_D(s)$, and $r\mapsto\mathrm{orb}_D(r)$ is a $k$-algebra homomorphism $R\to R[T]$.
--
--   In characteristic zero the map $\mathrm{orb}_D$ is the exponential $\exp(TD)$. It encodes the action of the additive group $(k,+)$ on $R$ determined by a locally nilpotent derivation, and specializing $T$ to an element of $k$ gives the automorphisms $\exp(aD)$. Its degree in $T$ is the $D$-degree of $r$, a basic invariant in the theory of locally nilpotent derivations.
--
--   **Formalization Note** Local nilpotence (`LocallyNilpotent D`) is stated with iterates `(D : R → R)^[n]`, so $n=0$ is allowed for $r=0$. The coefficient $1/n!$ is `((n.factorial : k)⁻¹)` acting by scalar multiplication, which is why the polynomial `orbit D hD r` is defined over any field. In positive characteristic Lean's convention $0^{-1}=0$ applies when $n!=0$ in $k$. Multiplicativity (`orbit_mul`) and the algebra homomorphism `orbitHom` require `CharZero k`. `iterate_zero`, `iterate_eq_zero_of_le` and `orbit_support_finite` are auxiliary.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/AffineCancellation/Orbit.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/AffineCancellation/Orbit.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ComplexCancellation mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ComplexCancellation
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderShift
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderMaps
import Definitions.Def_OAI_Algebra_AffineCancellation_Cylinder
import Definitions.Def_OAI_Algebra_AffineCancellation_Dimension
import Definitions.Def_OAI_Algebra_AffineCancellation_FactorDerivation

namespace OAI

noncomputable section

/-! Orbit polynomials and exponentiation of locally nilpotent derivations. -/
namespace ComplexCancellation.LND
open Polynomial

variable {k R : Type*} [Field k] [CommRing R] [Algebra k R]

/-- Local nilpotence, allowing the bound zero for the zero element. -/
def LocallyNilpotent (D : Derivation k R R) : Prop :=
  ∀ r : R, ∃ n : ℕ, (D : R → R)^[n] r = 0

lemma iterate_zero (D : Derivation k R R) (n : ℕ) : (D : R → R)^[n] 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, map_zero]

lemma iterate_eq_zero_of_le (D : Derivation k R R) {r : R} {n m : ℕ}
    (h : (D : R → R)^[n] r = 0) (hnm : n ≤ m) : (D : R → R)^[m] r = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hnm
  rw [Nat.add_comm, Function.iterate_add_apply, h, iterate_zero]

lemma iterate_leibniz (D : Derivation k R R) (n : ℕ) (r s : R) :
    (D : R → R)^[n] (r * s) =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
        n.choose ij.1 • ((D : R → R)^[ij.1] r * (D : R → R)^[ij.2] s) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, map_sum,
      Finset.sum_antidiagonal_choose_succ_nsmul
        (fun i j => (D : R → R)^[i] r * (D : R → R)^[j] s) n]
    simp only [map_nsmul, Derivation.leibniz, smul_eq_mul, nsmul_add,
      Finset.sum_add_distrib]
    congr 1
    · apply Finset.sum_congr rfl
      intro ij hij
      rw [Function.iterate_succ_apply']
    · apply Finset.sum_congr rfl
      rintro ⟨i,j⟩ hij
      have hij' : i + j = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
      have hchoose : n.choose i = n.choose j := by
        exact Nat.choose_symm_of_eq_add hij'.symm
      rw [Function.iterate_succ_apply', hchoose, mul_comm]

lemma orbit_support_finite (D : Derivation k R R) (hD : LocallyNilpotent D) (r : R) :
    (Function.support (fun n : ℕ => ((n.factorial : k)⁻¹) • (D : R → R)^[n] r)).Finite := by
  obtain ⟨m, hm⟩ := hD r
  apply (Set.finite_Iio m).subset
  intro n hn
  change n < m
  by_contra h
  have he := iterate_eq_zero_of_le D hm (by omega : m ≤ n)
  exact hn (by simp [he])

noncomputable def orbit (D : Derivation k R R) (hD : LocallyNilpotent D) (r : R) : R[X] :=
  Polynomial.ofFinsupp (AddMonoidAlgebra.ofCoeff
    (Finsupp.ofSupportFinite (fun n : ℕ => ((n.factorial : k)⁻¹) • (D : R → R)^[n] r)
      (orbit_support_finite D hD r)))

@[simp] lemma orbit_coeff (D : Derivation k R R) (hD : LocallyNilpotent D) (r : R) (n : ℕ) :
    (orbit D hD r).coeff n = ((n.factorial : k)⁻¹) • (D : R → R)^[n] r := by
  rfl

@[simp] lemma orbit_coeff_zero (D : Derivation k R R) (hD : LocallyNilpotent D) (r : R) :
    (orbit D hD r).coeff 0 = r := by simp

@[simp] lemma orbit_coeff_one (D : Derivation k R R) (hD : LocallyNilpotent D) (r : R) :
    (orbit D hD r).coeff 1 = D r := by simp

lemma inv_factorial_choose [CharZero k] {n i j : ℕ} (h : i + j = n) :
    ((n.factorial : k)⁻¹) * (n.choose i : k) =
      ((i.factorial : k)⁻¹) * ((j.factorial : k)⁻¹) := by
  have hi : i ≤ n := by omega
  rw [Nat.cast_choose k hi, show n - i = j by omega]
  have hn : (n.factorial : k) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  field_simp

lemma orbit_mul [CharZero k] (D : Derivation k R R) (hD : LocallyNilpotent D) (r s : R) :
    orbit D hD (r * s) = orbit D hD r * orbit D hD s := by
  ext n
  rw [orbit_coeff, Polynomial.coeff_mul, iterate_leibniz, Finset.smul_sum]
  apply Finset.sum_congr rfl
  rintro ⟨i,j⟩ hij
  rw [orbit_coeff, orbit_coeff]
  have hij' : i + j = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  rw [← Nat.cast_smul_eq_nsmul k, smul_smul, inv_factorial_choose hij',
    smul_mul_smul_comm]

lemma orbit_add (D : Derivation k R R) (hD : LocallyNilpotent D) (r s : R) :
    orbit D hD (r + s) = orbit D hD r + orbit D hD s := by
  ext n
  simp [smul_add]

lemma orbit_algebraMap (D : Derivation k R R) (hD : LocallyNilpotent D) (c : k) :
    orbit D hD (algebraMap k R c) = C (algebraMap k R c) := by
  ext n
  cases n with
  | zero => simp
  | succ n =>
    simp [Function.iterate_succ_apply, D.map_algebraMap]

noncomputable def orbitHom [CharZero k] (D : Derivation k R R) (hD : LocallyNilpotent D) : R →ₐ[k] R[X] where
  toFun := orbit D hD
  map_zero' := by ext; simp
  map_one' := by simpa using orbit_algebraMap D hD 1
  map_add' := orbit_add D hD
  map_mul' := orbit_mul D hD
  commutes' := orbit_algebraMap D hD

end ComplexCancellation.LND

end

end OAI


