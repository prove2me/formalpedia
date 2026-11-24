-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_FockPairingHighestWeight
-- name    : Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_FockPairingHighestWeight
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T07:05:54.310118+00:00
-- url     : https://prove2.me/theorems/6c604a89-faf8-4842-a75e-8d8b0bcf331f
-- title:
--   Fock Pairing Highest Weight
-- statement:
--   Definitions and structural lemmas for Fock Pairing Highest Weight, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/FockPairingHighestWeight.lean

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_FockR
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open scoped Classical
noncomputable section
namespace Formalism.L2.G.Model.TS
open Formalism.GradedWeylDivisibility
def FockRBilin : Prop :=
  ∀ (σ R : Type) [CommRing R] (f f' g : MvPolynomial σ R) (a : R),
    fockR (f + f') g = fockR f g + fockR f' g ∧ fockR (a • f) g = a * fockR f g ∧ fockR f g = fockR g f
def FockRMap : Prop :=
  ∀ (σ R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (f g : MvPolynomial σ R),
    fockR (map φ f) (map φ g) = φ (fockR f g)
def FockRMonomial : Prop :=
  ∀ (σ R : Type) [CommRing R] (m m' : σ →₀ ℕ) (a b : R),
    fockR (monomial m a) (monomial m' b) = if m = m' then a * b * ((∏ k ∈ m.support, (m k).factorial : ℕ) : R) else 0
def FockRBlock : Prop :=
  ∀ (K S : Type) [CommRing K] [Fintype S] (k n : ℕ) (F G : S → MvPolynomial (Fin k × Fin n) K),
    fockR (∏ s, blockEmb K s (F s)) (∏ s, blockEmb K s (G s)) = ∏ s, fockR (F s) (G s)
def FockRRowDivAdj : Prop :=
  ∀ (R : Type) [CommRing R] (r n : ℕ) (a b : Fin r) (k : ℕ) (f g : MvPolynomial (Fin r × Fin n) R),
    fockR (rowDiv R a b k f) g = fockR f (rowDiv R b a k g)
def FockRWordAdj : Prop :=
  ∀ (R : Type) [CommRing R] (r n : ℕ) (w : List (Fin r × Fin r × ℕ)) (F G : MvPolynomial (Fin r × Fin n) R),
    fockR (applyWord R w F) G = fockR F (applyWord R (transposeWord w) G)
def FockRRowAct : Prop :=
  ∀ (R : Type) [CommRing R] (r n : ℕ) (g : Matrix (Fin r) (Fin r) R) (P Q : MvPolynomial (Fin r × Fin n) R),
    fockR (rowAct R g P) Q = fockR P (rowAct R g.transpose Q)
def HWNorm : Prop :=
  ∀ (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ), ∃ N : ℕ, 0 < N ∧
    ∀ (R : Type) [CommRing R], fockR (hw R hn ν) (hw R hn ν) = (N : R)
def FockPairingHighestWeight : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ), Antitone ν → ∀ F ∈ dualWeyl K r n ν,
    fockR (hw K hn ν) F = eval (idFrame K r n) F * fockR (hw K hn ν) (hw K hn ν)
def LowerTriK : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K] (r n : ℕ) (ν : Fin n → ℕ)
    (Q : MvPolynomial (Fin r × Fin n) K), Q ∈ dualWeyl K r n ν →
    ((∀ e : Fin r × Fin n →₀ ℕ, LowerTri e → coeff e Q ∈ Set.range (algebraMap O K)) →
      Q ∈ (dualWeyl O r n ν).map (toK O K)) ∧
    ((∀ e : Fin r × Fin n →₀ ℕ, LowerTri e → coeff e Q = 0) → Q = 0)
end Formalism.L2.G.Model.TS


