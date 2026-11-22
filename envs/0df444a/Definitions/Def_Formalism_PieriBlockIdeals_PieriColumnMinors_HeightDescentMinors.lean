-- Prove2me | Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
-- name    : Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:16:47.320901+00:00
-- url     : https://prove2.me/theorems/b02f8bc7-587f-43c8-ab15-93b133d328cc
-- title:
--   Height Descent Minors
-- statement:
--   Definitions and structural lemmas for Height Descent Minors, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset PowerSeries
namespace Formalism.CohomologicalDescent.HeightDescentMinors
section PartA
section Ode
variable {R : Type*} [CommRing R]
variable [BinomialRing R]
end Ode
section Act
variable (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
end Act
section Mu
variable (l : ℕ) [Fact l.Prime]
variable (O : Type) [CommRing O] [Algebra ℤ_[l] O]
end Mu
end PartA
section PartA2
section A2General
end A2General
section A2
variable (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
end A2
section A2R3
variable (l : ℕ) [Fact l.Prime]
end A2R3
end PartA2
section PartB
section General
variable {R : Type} [CommRing R]
def divQuotient (n : ℕ) (w : (R⟦X⟧)ˣ) (f : R⟦X⟧) : R⟦X⟧ :=
  ((w⁻¹ : (R⟦X⟧)ˣ) : R⟦X⟧) * PowerSeries.mk fun i => coeff (i + n) f
end General
section General2
variable {R : Type} [CommRing R]
end General2
section Pi0
variable (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
end Pi0
end PartB
section PartB2
section
variable (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
end
end PartB2
section PartC
section CapelliProof
variable {𝒰 : Type} [Ring 𝒰]
def orderedProd {N : ℕ} (a : Fin N → 𝒰) : 𝒰 := (List.ofFn a).prod
def columnDet {N : ℕ} (c : Fin N → Fin N → 𝒰) : 𝒰 :=
  ∑ σ : Equiv.Perm (Fin N), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) • orderedProd (fun p => c p (σ p))
def columnDetAt {N : ℕ} (E : Fin N → Fin N → 𝒰) (u : 𝒰) (J : Fin N → Fin N) : 𝒰 :=
  columnDet (fun p s => capA E (u - ((p : ℕ) : 𝒰)) s (J p))
end CapelliProof
end PartC
section PartD
end PartD
section PartE
section PartE
variable {R : Type} [CommRing R]
end PartE
end PartE
section PartG
section Lin
variable {O : Type} [CommRing O] [IsDomain O] (I : Ideal O) [IsAdicComplete I O] (c : O)
end Lin
end PartG
section PartH
end PartH
section PartC2
section HW
variable {k : Type} [CommRing k] {𝒰 : Type} [Ring 𝒰] [Algebra k 𝒰] {V : Type} [AddCommGroup V]
  [Module k V] [Module 𝒰 V] [IsScalarTower k 𝒰 V]
end HW
attribute [local instance 100] LieRing.ofAssociativeRing
end PartC2
end Formalism.CohomologicalDescent.HeightDescentMinors


