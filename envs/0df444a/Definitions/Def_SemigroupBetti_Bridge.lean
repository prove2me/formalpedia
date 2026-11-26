-- Prove2me | Definitions.Def_SemigroupBetti_Bridge
-- name    : SemigroupBetti_Bridge
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T02:52:13.980467+00:00
-- url     : https://prove2.me/theorems/2ef25540-4627-51fc-b43b-1785d4693454
-- title:
--   Bridge
-- statement:
--   Definitions and structural lemmas for Bridge, from Ben Keene (BenKeene/semigroup-betti; see pinned Apache-2.0 LICENSE and source headers)'s pinned Linear upper bound for the first Betti number of four-generated numerical semigroups development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Bridge.lean

module
public import Definitions.Def_SemigroupBetti_Fiber
public import Theorems.Thm_SemigroupBetti_GenData_mem_fiber
public import Theorems.Thm_SemigroupBetti_GenData_n_one
public import Theorems.Thm_SemigroupBetti_GenData_n_three
public import Theorems.Thm_SemigroupBetti_GenData_n_two
public import Theorems.Thm_SemigroupBetti_GenData_n_zero
public import Theorems.Thm_SemigroupBetti_GenData_nu_zero
public import Theorems.Thm_SemigroupBetti_SharesVar_symm
public import Theorems.Thm_SemigroupBetti_mem_supp
attribute [local simp] SemigroupBetti.GenData.mem_fiber
attribute [local simp] SemigroupBetti.GenData.n_one
attribute [local simp] SemigroupBetti.GenData.n_three
attribute [local simp] SemigroupBetti.GenData.n_two
attribute [local simp] SemigroupBetti.GenData.n_zero
attribute [local simp] SemigroupBetti.GenData.nu_zero
attribute [local simp] SemigroupBetti.mem_supp


set_option autoImplicit false
@[expose] public section
@[expose] public section
namespace SemigroupBetti
open Finset MvPolynomial
section Mono
variable (K : Type*) [Field K]
noncomputable def mono (z : Fin 4 → ℕ) : MvPolynomial (Fin 4) K :=
  monomial (Finsupp.equivFunOnFinite.symm z) 1
noncomputable def toricMap (n : Fin 4 → ℕ) : MvPolynomial (Fin 4) K →ₐ[K] Polynomial K :=
  aeval (fun i => (Polynomial.X : Polynomial K) ^ n i)
variable {K}
end Mono
namespace GenData
variable (G : GenData) (K : Type*) [Field K]
noncomputable abbrev toricKer : Ideal (MvPolynomial (Fin 4) K) :=
  RingHom.ker (MvPolynomial.aeval (fun i => (Polynomial.X : Polynomial K) ^ G.n i)).toRingHom
noncomputable def rep {d : ℕ} (C : (G.nabla d).ConnectedComponent) : Fin 4 → ℕ :=
  (Quot.out C : G.fiber d).1
open Classical in
/-- The chosen binomials of degree `d`: `X^{rep C} - X^{rep C₀}` for `C ≠ C₀`, where `C₀` is
a fixed base component (none if the fiber is empty). -/
noncomputable def genSet (d : ℕ) : Finset (MvPolynomial (Fin 4) K) :=
  if h : Nonempty (G.nabla d).ConnectedComponent then
    (univ.erase (Classical.choice h)).image
      (fun C => mono K (G.rep C) - mono K (G.rep (Classical.choice h)))
  else ∅
open Classical in
/-- All chosen binomials, over the degrees `d ≤ H`. -/
noncomputable def binomGens : Finset (MvPolynomial (Fin 4) K) :=
  (range (G.H + 1)).biUnion (G.genSet K)
open Classical in
/-- A chosen factorization of `d` (junk `0` when the fiber is empty). -/
noncomputable def root (d : ℕ) : Fin 4 → ℕ :=
  if h : (G.fiber d).Nonempty then h.choose else 0
end GenData
namespace GenData
def ofChallenge (n : Fin 4 → ℕ) (hpos : 0 < n 0) (hmono : StrictMono n)
    (hgcd : Finset.univ.gcd n = 1)
    (hmin : ∀ i : Fin 4, n i ∉ AddSubmonoid.closure (n '' {j | j ≠ i})) : GenData :=
  have h01 : n 0 < n 1 := hmono (by decide)
  have h12 : n 1 < n 2 := hmono (by decide)
  have h23 : n 2 < n 3 := hmono (by decide)
  have hgens : gens (n 0) (n 1 - n 0) (n 2 - n 0) (n 3 - n 0) = n := by
    funext i; fin_cases i <;> simp [gens] <;> omega
  { m := n 0
    a := n 1 - n 0
    b := n 2 - n 0
    w := n 3 - n 0
    m_pos := hpos
    a_pos := by omega
    a_lt_b := by omega
    b_lt_w := by omega
    gcd_eq_one := by
      set g := Nat.gcd (n 0) (Nat.gcd (n 1 - n 0) (Nat.gcd (n 2 - n 0) (n 3 - n 0)))
      have h0 : g ∣ n 0 := Nat.gcd_dvd_left _ _
      have ha : g ∣ n 1 - n 0 := (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _)
      have hb : g ∣ n 2 - n 0 :=
        (Nat.gcd_dvd_right _ _).trans ((Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _))
      have hw : g ∣ n 3 - n 0 :=
        (Nat.gcd_dvd_right _ _).trans ((Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _))
      have hall : ∀ i ∈ (Finset.univ : Finset (Fin 4)), g ∣ n i := by
        intro i _
        fin_cases i
        · exact h0
        · have : n 1 = n 0 + (n 1 - n 0) := by omega
          simpa [← this] using Nat.dvd_add h0 ha
        · have : n 2 = n 0 + (n 2 - n 0) := by omega
          simpa [← this] using Nat.dvd_add h0 hb
        · have : n 3 = n 0 + (n 3 - n 0) := by omega
          simpa [← this] using Nat.dvd_add h0 hw
      have := Finset.dvd_gcd hall
      rw [hgcd] at this
      exact Nat.dvd_one.1 this
    minimal := by
      intro i z hzi heq
      rw [hgens] at heq
      apply hmin i
      rw [← heq]
      refine AddSubmonoid.sum_mem _ fun j _ => ?_
      by_cases hj : j = i
      · subst hj; rw [hzi, zero_mul]; exact zero_mem _
      · rw [← smul_eq_mul]
        exact AddSubmonoid.nsmul_mem _ (AddSubmonoid.subset_closure (Set.mem_image_of_mem n (show j ∈ {j | j ≠ i} from hj))) _ }
section
variable (n : Fin 4 → ℕ) (hpos : 0 < n 0) (hmono : StrictMono n)
  (hgcd : Finset.univ.gcd n = 1)
  (hmin : ∀ i : Fin 4, n i ∉ AddSubmonoid.closure (n '' {j | j ≠ i}))
end
end GenData
end SemigroupBetti


