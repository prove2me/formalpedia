-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipNormOne
-- name    : Formalism_LocalToGlobal_CharacterGerms_BlockMembershipNormOne
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T00:32:27.540794+00:00
-- url     : https://prove2.me/theorems/ac0ec2e0-af2e-46fa-bed0-00f4776df58a
-- title:
--   Block Membership Norm One
-- statement:
--   Definitions and structural lemmas for Block Membership Norm One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/BlockMembershipNormOne.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValBlocksChart
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RowDeg
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
namespace Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds Formalism.L2.Pj
abbrev IIof {T Orb : Type} {d : ℕ} (r : T → ℕ) (tau : Orb → Fin 2 → ZMod d → T) (o : Orb) (g : Fin 2) : Type :=
  Σ t : ZMod d, Fin (r (tau o g t))
def phiL {T Orb : Type} {d : ℕ} (r : T → ℕ) (tau : Orb → Fin 2 → ZMod d → T) (n : ℕ)
    (x : Fin n × WVO (IIof r tau)) : Letter T r n :=
  ⟨tau x.2.1 x.2.2.1 x.2.2.2.1, x.2.2.2.2, x.1⟩
def WtTie {T Orb : Type} {d : ℕ} (r : T → ℕ) (tau : Orb → Fin 2 → ZMod d → T) (Z : Finset Orb)
    (ga : Orb → Fin 2 → ZMod d → ℕ → ℕ) (a : T → ℕ → ℕ) : Prop :=
  (∀ o ∈ Z, ∀ g t (i : ℕ), i < r (tau o g t) →
    a (tau o g t) i = ∑ k ∈ Finset.Icc (i + 1) (r (tau o g t)), ga o g t k) ∧
  ∀ σ, (∀ o ∈ Z, ∀ g t, tau o g t ≠ σ) → ∀ i, i < r σ → a σ i = 0
section Defs
variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {Orb : Type} [Fintype Orb]
  {I J : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)] [∀ o g, Fintype (J o g)]
def blkProd (X : ∀ o, RowData C V d (I o) (J o)) (F : ∀ o, Flag (X o)) (n : ℕ) (L : Orb → List (GlobalTheory d × ℝ))
    (pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin n) : MvPolynomial (Fin n × WVO I) C :=
  ∏ o, toAll o (prodAll (plAt n pl o) fun i => (blkAt L o i).poly (X o) (F o))
end Defs
structure ConjugatePairPlaceSetting {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {T : Type} (r : T → ℕ) (cc : T → T) (a : T → ℕ → ℕ)
    {Orb : Type} [Fintype Orb] (tau : Orb → Fin 2 → ZMod d → T) {J : Orb → Fin 2 → Type} [∀ o g, Fintype (J o g)]
    (X : ∀ o, RowData C V d (IIof r tau o) (J o)) (F : ∀ o, Flag (X o)) (Z : Finset Orb)
    (ga : Orb → Fin 2 → ZMod d → ℕ → ℕ) (n : ℕ) (L : Orb → List (GlobalTheory d × ℝ))
    (pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin n) : Prop where

  inj : Function.Injective fun x : Orb × Fin 2 × ZMod d => tau x.1 x.2.1 x.2.2
  conj : ∀ o t, cc (tau o 0 t) = tau o 1 t
  conj' : ∀ o t, cc (tau o 1 t) = tau o 0 t

  hty : ∀ o g (x : IIof r tau o g), ((X o).G g).ty (Sum.inl x) = x.1
  std : ∀ o g t (c : Fin ((X o).rkF g t)), ((F o).en g t c).2.val = c.val

  dich : ∀ o ∈ Z, (X o).Alt ∨ ∀ t, (X o).big 0 t
  hj : ∀ o ∈ Z, (X o).j' < (X o).n
  supp : ∀ o ∈ Z, ∀ g t k, ga o g t k ≠ 0 → 1 ≤ k ∧ k ≤ (X o).rkF g t

  off : ∀ o, o ∉ Z → L o = []
  wt : ∀ o ∈ Z, ∀ g t k, ((L o).map fun q => q.1.wt (X o) g t k).sum = ga o g t k
  tie : WtTie r tau Z ga a
  plinj : Function.Injective pl
def NormOneHarmonic : Prop :=
  ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (T : Type) (r : T → ℕ) (cc : T → T) (a : T → ℕ → ℕ)
    (Orb : Type) [Fintype Orb] (tau : Orb → Fin 2 → ZMod d → T) (J : Orb → Fin 2 → Type) [∀ o g, Fintype (J o g)]
    (X : ∀ o, RowData C V d (IIof r tau o) (J o)) (F : ∀ o, Flag (X o)) (Z : Finset Orb)
    (ga : Orb → Fin 2 → ZMod d → ℕ → ℕ) (n : ℕ) (L : Orb → List (GlobalTheory d × ℝ))
    (pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin n),
    ConjugatePairPlaceSetting r cc a tau X F Z ga n L pl →
      ∀ isX : T → Prop, MvPolynomial.rename (phiL r tau n) (blkProd X F n L pl) ∈ harmK r n C cc isX (fun _ => 1)
def NormOneLineInvariant : Prop :=
  ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (T : Type) (r : T → ℕ) (cc : T → T) (a : T → ℕ → ℕ)
    (Orb : Type) [Fintype Orb] (tau : Orb → Fin 2 → ZMod d → T) (J : Orb → Fin 2 → Type) [∀ o g, Fintype (J o g)]
    (X : ∀ o, RowData C V d (IIof r tau o) (J o)) (F : ∀ o, Flag (X o)) (Z : Finset Orb)
    (ga : Orb → Fin 2 → ZMod d → ℕ → ℕ) (n : ℕ) (L : Orb → List (GlobalTheory d × ℝ))
    (pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin n),
    ConjugatePairPlaceSetting r cc a tau X F Z ga n L pl →
      RowInv r n C (MvPolynomial.rename (phiL r tau n) (blkProd X F n L pl))
def NormOneLineDegrees : Prop :=
  ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (T : Type) (r : T → ℕ) (cc : T → T) (a : T → ℕ → ℕ)
    (Orb : Type) [Fintype Orb] (tau : Orb → Fin 2 → ZMod d → T) (J : Orb → Fin 2 → Type) [∀ o g, Fintype (J o g)]
    (X : ∀ o, RowData C V d (IIof r tau o) (J o)) (F : ∀ o, Flag (X o)) (Z : Finset Orb)
    (ga : Orb → Fin 2 → ZMod d → ℕ → ℕ) (n : ℕ) (L : Orb → List (GlobalTheory d × ℝ))
    (pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin n),
    ConjugatePairPlaceSetting r cc a tau X F Z ga n L pl →
      RowDeg r n C a (MvPolynomial.rename (phiL r tau n) (blkProd X F n L pl))
def NormOneIntegral : Prop :=
  ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (T : Type) (r : T → ℕ) (cc : T → T) (a : T → ℕ → ℕ)
    (Orb : Type) [Fintype Orb] (tau : Orb → Fin 2 → ZMod d → T) (J : Orb → Fin 2 → Type) [∀ o g, Fintype (J o g)]
    (X : ∀ o, RowData C V d (IIof r tau o) (J o)) (F : ∀ o, Flag (X o)) (Z : Finset Orb)
    (ga : Orb → Fin 2 → ZMod d → ℕ → ℕ) (n : ℕ) (L : Orb → List (GlobalTheory d × ℝ))
    (pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin n),
    ConjugatePairPlaceSetting r cc a tau X F Z ga n L pl →
      ∀ (O : Subring C) m, (MvPolynomial.rename (phiL r tau n) (blkProd X F n L pl)).coeff m ∈ O
section Mem
variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {T : Type} (r : T → ℕ) (cc : T → T) (isX : T → Prop)
  (a : T → ℕ → ℕ) {Orb : Type} [Fintype Orb] (tau : Orb → Fin 2 → ZMod d → T) (O : Subring C) (n : ℕ)
def harmonicProductFamily : Set (∀ o, MvPolynomial (Fin n × WV (IIof r tau o)) C) :=
  {Po | MvPolynomial.rename (phiL r tau n) (∏ o, toAll o (Po o)) ∈ HaO r n C O cc isX a}
variable {J : Orb → Fin 2 → Type} [∀ o g, Fintype (J o g)]
end Mem
end Formalism.L2.FormalSeriesBounds.RF


