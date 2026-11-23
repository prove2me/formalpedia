-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
-- name    : ReciprocityTheory_DualLattices_TowerZeroSurjective
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:48:47.87832+00:00
-- url     : https://prove2.me/theorems/0cc7f54e-20fd-443d-aab5-347457e4dfe4
-- title:
--   Tower Zero Surjective
-- statement:
--   Definitions and structural lemmas for Tower Zero Surjective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/TowerZeroSurjective.lean

import Definitions.Def_ReciprocityTheory_DualLattices_FormalChartAtZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct IsLocalRing Matrix
namespace ReciprocityTheory.PGsh.Be2
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2
variable {R₀ : Type} [CommRing R₀]
structure Dat (p : ℕ) [Fact p.Prime] (g : ℕ) (B : BX R₀) (Tw : ATowerL R₀ p) (Dt : DualTower Tw)
    [Algebra ℤ_[p] (Tw.O : Type)] (Oe : Type) [CommRing Oe] [Algebra ℤ_[p] Oe] (σ : Oe ≃ₐ[ℤ_[p]] Oe)
    (cp : (Tw.O : Type)) where
  K : LAlg R₀
  ρO : LHom Tw.O K
  ch : FormalChartAtZero B K g
  wd : WData Tw K

  ρO_eq : wd.ρ1.comp (Tw.q 0) = ρO
  sm : SM B K wd.W wd.ρW
  fin : FIN B Tw.O p
  A : OAct B Tw.O p Oe
  H : HodgeTateData p g (Tw.O : Type) Oe σ cp
  L : Link B Tw Dt H ch.gb A

  tower_zero_surjective : Function.Surjective (Tw.q 0).1

  tower_zero_ker : RingHom.ker (Tw.q 0).1 = Ideal.span {((p : ℕ) : (Tw.O : Type))}

  zeta0 : p = 2 → ((Tw.ζ 0 : (Tw.O : Type)ˣ) : (Tw.O : Type)) = -1
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw}
  [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe}
  {cp : (Tw.O : Type)}
namespace Dat
variable (D : Dat p g B Tw Dt Oe σ cp)
lemma pt_p (t : Nb p g) : p • ptOf B D.L.τ t = 0 := by
  have h0 : ∀ j, p • D.L.τ j 0 = 0 := fun j => by simpa using D.L.τ_tors j 0
  simp only [ptOf, Finset.smul_sum]
  exact Finset.sum_eq_zero fun j _ => by rw [smul_comm, h0, smul_zero]
def ptIdx (t : Nb p g) : D.fin.ι :=
  Classical.choose (D.fin.univ Tw.O (LHom.id Tw.O) (ptOf B D.L.τ t) (D.pt_p t))
def ptMap (t : Nb p g) : LHom (D.fin.AAx (D.ptIdx t)) Tw.O :=
  Classical.choose (Classical.choose_spec
    (D.fin.univ Tw.O (LHom.id Tw.O) (ptOf B D.L.τ t) (D.pt_p t)))
def evAll (C : Type) [Field C] [Algebra (Tw.O : Type) C] (F : ∀ i, (D.fin.AAx i : Type)) :
    Nb p g → C :=
  fun t => algebraMap (Tw.O : Type) C ((D.ptMap t).1 (F (D.ptIdx t)))
def evImg (C : Type) [Field C] [Algebra (Tw.O : Type) C] : Submodule (Tw.O : Type) (Nb p g → C) :=
  Submodule.span (Tw.O : Type) (Set.range (D.evAll C))
end Dat
end ReciprocityTheory.PGsh.Be2


