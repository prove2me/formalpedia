-- Prove2me | Definitions.Def_RPLib_S4_EtShInertiaLift2
-- name    : RPLib_S4_EtShInertiaLift2
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T07:18:31.116491+00:00
-- url     : https://prove2.me/theorems/901e000b-319f-4965-9c4c-df32bd7e242d
-- title:
--   The inertia lift
-- statement:
--   Let $A \subseteq B$ with $B$ an integrally closed domain, $L = \mathrm{Frac}\,B$ Galois over $K = \mathrm{Frac}\,A$, and $\tau \in \mathrm{Gal}(L/K)$ acting on $B$ with $\tau(b) - b \in Q$ for all $b \in B$ (inertia at the prime $Q$). Let $R'$ be a standard etale $A$-algebra with a prime $\mathfrak u$ over $Q \cap A$. Then for every separably closed field $\Omega$ normal over $K$ there are $A$-algebra maps $\psi : R' \to \Omega$, $\iota : L \to \Omega$ over $K$ and $\tau' \in \mathrm{Aut}(\Omega/K)$ with $$\tau' \circ \psi = \psi, \qquad \tau' \circ \iota = \iota \circ \tau.$$
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale sheaves of $\Lambda$-modules on Mathlib's small etale site, geometric points, stalks and the Galois action on generic stalks). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J. Neukirch, Algebraic Number Theory, Grundlehren 322, Springer (1999), Chapter I, Section 9; M. Raynaud, Anneaux locaux henseliens, Lecture Notes in Math. 169, Springer (1970), Chapters V and VIII

import Mathlib
import Definitions.Def_RPLib_S4_EtShInertiaLift

/-!
# S4-EtSheaves, O10c part 2d: the inertia lift

HEADLINE `exists_inertia_lift`: let `τ ∈ Gal(L/K)` act on `B` (`Frac B = L`, `B` integrally closed)
through `τB` with `τB b - b ∈ Q` for all `b` (inertia at `Q`), and let `R'` be standard etale over `A`
with a prime `u` over `Q ∩ A`. Then for any separably closed `Ω` normal over `K` there are
`ψ : R' →ₐ[A] Ω`, `ι : L →ₐ[K] Ω` and `τ' ∈ Aut(Ω/K)` with `τ' ∘ ψ = ψ` and `τ' ∘ ι = ι ∘ τ`.
-/

set_option autoImplicit false

open Polynomial TensorProduct

noncomputable section

namespace RamanujanPetersson.EtSheaves.InertiaLift

variable {A K L B R' : Type*} [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K]
  [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
  [CommRing B] [IsDomain B] [Algebra A B] [Algebra B L] [IsScalarTower A B L] [IsFractionRing B L]
  [CommRing R'] [Algebra A R']

/-- The lift for a fixed branch `𝔭` of `B ⊗[A] R'` over `(0)` with `(τB ⊗ 1)⁻¹ 𝔭 = 𝔭`. -/
theorem exists_lift [Algebra.IsSeparable K L] (P0 : StandardEtalePresentation A R')
    (τ : L ≃ₐ[K] L) (τB : B ≃ₐ[A] B) (hτB : ∀ b, algebraMap B L (τB b) = τ (algebraMap B L b))
    (𝔭 : Ideal (B ⊗[A] R')) [𝔭.IsPrime] (h0 : 𝔭.comap (algebraMap B (B ⊗[A] R')) = ⊥)
    (hfix : 𝔭.comap (InertiaFix.tauT τB) = 𝔭)
    (Ω : Type*) [Field Ω] [Algebra K Ω] [Algebra A Ω] [IsScalarTower A K Ω] [IsSepClosed Ω]
    [Normal K Ω] :
    ∃ ψ : R' →ₐ[A] Ω, ∃ ι : L →ₐ[K] Ω, ∃ τ' : Ω ≃ₐ[K] Ω,
      (∀ r, τ' (ψ r) = ψ r) ∧ ∀ l, τ' (ι l) = ι (τ l) := by
  have hinj := algebraMap_injective 𝔭 h0
  let lam : L →+* Fld 𝔭 := IsFractionRing.lift (A := B) (K := L) hinj
  have hlam : ∀ b, lam (algebraMap B L b) = algebraMap B (Fld 𝔭) b :=
    IsFractionRing.lift_algebraMap hinj
  letI : Algebra L (Fld 𝔭) := lam.toAlgebra
  letI : Algebra K (Fld 𝔭) := (lam.comp (algebraMap K L)).toAlgebra
  haveI : IsScalarTower K L (Fld 𝔭) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower B L (Fld 𝔭) := IsScalarTower.of_algebraMap_eq (fun b => (hlam b).symm)
  haveI : IsScalarTower A L (Fld 𝔭) := IsScalarTower.of_algebraMap_eq (fun a => by
    show algebraMap A (Fld 𝔭) a = lam (algebraMap A L a)
    rw [IsScalarTower.algebraMap_apply A B L, hlam, ← IsScalarTower.algebraMap_apply])
  haveI : IsScalarTower A K (Fld 𝔭) := IsScalarTower.of_algebraMap_eq (fun a => by
    show algebraMap A (Fld 𝔭) a = lam (algebraMap K L (algebraMap A K a))
    rw [← IsScalarTower.algebraMap_apply A K L, IsScalarTower.algebraMap_apply A B L, hlam,
      ← IsScalarTower.algebraMap_apply])
  haveI : Algebra.IsSeparable L (Fld 𝔭) := isSeparable_frac 𝔭 P0 (Fld 𝔭)
  haveI : Algebra.IsSeparable K (Fld 𝔭) := Algebra.IsSeparable.trans K L (Fld 𝔭)
  have hIJ : 𝔭 = 𝔭.map ((InertiaFix.tauT τB : B ⊗[A] R' ≃ₐ[A] B ⊗[A] R') :
      B ⊗[A] R' →+* B ⊗[A] R') := by
    have h := Ideal.map_comap_of_surjective (InertiaFix.tauT (R' := R') τB)
      (InertiaFix.tauT τB).surjective 𝔭
    rw [hfix] at h
    exact h.symm
  let τD := Ideal.quotientEquivAlg 𝔭 𝔭 (InertiaFix.tauT τB) hIJ
  let τE : Fld 𝔭 ≃ₐ[K] Fld 𝔭 := IsFractionRing.fieldEquivOfAlgEquiv K (Fld 𝔭) (Fld 𝔭) τD
  have hτE : ∀ s, τE (algebraMap (B ⊗[A] R' ⧸ 𝔭) (Fld 𝔭) (Ideal.Quotient.mk 𝔭 s)) =
      algebraMap (B ⊗[A] R' ⧸ 𝔭) (Fld 𝔭) (Ideal.Quotient.mk 𝔭 (InertiaFix.tauT τB s)) := by
    intro s
    rw [IsFractionRing.fieldEquivOfAlgEquiv_algebraMap]
    exact congrArg _ (Ideal.quotientEquivAlg_mk 𝔭 (InertiaFix.tauT τB) hIJ s)
  have hB : ∀ b, τE (algebraMap B (Fld 𝔭) b) = algebraMap B (Fld 𝔭) (τB b) := by
    intro b
    rw [IsScalarTower.algebraMap_apply B (B ⊗[A] R' ⧸ 𝔭) (Fld 𝔭),
      IsScalarTower.algebraMap_apply B (B ⊗[A] R' ⧸ 𝔭) (Fld 𝔭) (τB b),
      ← Ideal.Quotient.mk_algebraMap, ← Ideal.Quotient.mk_algebraMap, hτE,
      InertiaFix.tauT_algebraMap]
  have hlamτ : ∀ l, τE (lam l) = lam (τ l) := by
    have h : (τE : Fld 𝔭 →+* Fld 𝔭).comp lam = lam.comp (τ : L →+* L) := by
      apply IsLocalization.ringHom_ext (nonZeroDivisors B)
      ext b
      show τE (lam (algebraMap B L b)) = lam (τ (algebraMap B L b))
      rw [hlam, hB, ← hτB, hlam]
    intro l
    exact congrArg (fun φ : L →+* Fld 𝔭 => φ l) h
  let ρ : R' →ₐ[A] Fld 𝔭 := (IsScalarTower.toAlgHom A (B ⊗[A] R' ⧸ 𝔭) (Fld 𝔭)).comp
    ((Ideal.Quotient.mkₐ A 𝔭).comp Algebra.TensorProduct.includeRight)
  have hρ : ∀ r, τE (ρ r) = ρ r := by
    intro r
    show τE (algebraMap (B ⊗[A] R' ⧸ 𝔭) (Fld 𝔭) (Ideal.Quotient.mk 𝔭 ((1 : B) ⊗ₜ r))) =
      algebraMap (B ⊗[A] R' ⧸ 𝔭) (Fld 𝔭) (Ideal.Quotient.mk 𝔭 ((1 : B) ⊗ₜ r))
    rw [hτE, InertiaFix.tauT_tmul, map_one]
  obtain ⟨j, τ', hj⟩ := exists_lift_aut (Ω := Ω) τE
  refine ⟨(j.restrictScalars A).comp ρ, j.comp (IsScalarTower.toAlgHom K L (Fld 𝔭)), τ',
    fun r => ?_, fun l => ?_⟩
  · show τ' (j (ρ r)) = j (ρ r)
    rw [hj, hρ]
  · show τ' (j (lam l)) = j (lam (τ l))
    rw [hj, hlamτ]

/-- HEADLINE (O10c F2): an inertia element at `Q` lifts to `Aut(Ω/K)` fixing an `Ω`-point of `R'`. -/
theorem exists_inertia_lift [Algebra.IsSeparable K L] [IsIntegrallyClosed B]
    (P0 : StandardEtalePresentation A R') (τ : L ≃ₐ[K] L) (τB : B ≃ₐ[A] B)
    (hτB : ∀ b, algebraMap B L (τB b) = τ (algebraMap B L b)) (Q : Ideal B) [Q.IsPrime]
    (hτ : ∀ b, τB b - b ∈ Q) (u : Ideal R') [u.IsPrime]
    (hu : u.comap (algebraMap A R') = Q.comap (algebraMap A B))
    (Ω : Type*) [Field Ω] [Algebra K Ω] [Algebra A Ω] [IsScalarTower A K Ω] [IsSepClosed Ω]
    [Normal K Ω] :
    ∃ ψ : R' →ₐ[A] Ω, ∃ ι : L →ₐ[K] Ω, ∃ τ' : Ω ≃ₐ[K] Ω,
      (∀ r, τ' (ψ r) = ψ r) ∧ ∀ l, τ' (ι l) = ι (τ l) := by
  obtain ⟨𝔮, h𝔮p, h𝔮⟩ := FibreNe.exists_prime_tmul Q u hu
  haveI := h𝔮p
  obtain ⟨𝔭, h𝔭p, -, h0, hfix⟩ := InertiaFix.exists_fixed_prime P0 τB Q hτ 𝔮 h𝔮
  haveI := h𝔭p
  exact exists_lift P0 τ τB hτB 𝔭 h0 hfix Ω

end RamanujanPetersson.EtSheaves.InertiaLift


