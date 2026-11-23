-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_MemVarsProdAll
-- name    : Formalism_LocalToGlobal_CharacterGerms_MemVarsProdAll
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:26:49.404732+00:00
-- url     : https://prove2.me/theorems/849108e1-b24c-49e0-80a4-1a0e334b0acc
-- title:
--   Mem Vars Prod All
-- statement:
--   Definitions and structural lemmas for Mem Vars Prod All, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/MemVarsProdAll.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_Interface
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
namespace Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds
abbrev Knd (d : ℕ) := Option (Fin 2 × ZMod d × ZMod d)
section Place
variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} {N K : ℕ} {what₂ : Fin K → ℕ}
def kindAll (pl : (Σ i : Fin K, Fin (what₂ i)) → Fin N) (kind : ∀ i, Fin (what₂ i) → Knd d) (ρ : Fin N) : Knd d :=
  if h : ∃ s, pl s = ρ then kind h.choose.1 h.choose.2 else none
def grAll (pl : (Σ i : Fin K, Fin (what₂ i)) → Fin N) (gr : ∀ i, Fin (what₂ i) → MvPowerSeries (WV I) C) (ρ : Fin N) :
    MvPowerSeries (WV I) C :=
  if h : ∃ s, pl s = ρ then gr h.choose.1 h.choose.2 else 1
def prodAll (pl : (Σ i : Fin K, Fin (what₂ i)) → Fin N) (P : ∀ i, MvPolynomial (Fin (what₂ i) × WV I) C) :
    MvPolynomial (Fin N × WV I) C :=
  ∏ i, MvPolynomial.rename (fun x : Fin (what₂ i) × WV I => (pl ⟨i, x.1⟩, x.2)) (P i)
end Place
section Rows
variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Fin 2 → Type} [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]
  {N K : ℕ} {what₂ : Fin K → ℕ}
end Rows
def JetProdSt : Prop :=
  ∀ (C : Type) [Field C] (d : ℕ) (I : Fin 2 → Type) [∀ g, Fintype (I g)]
    (hL : Fin 2 → ZMod d → ZMod d → MvPowerSeries (WV I) C) (N K : ℕ) (what₂ : Fin K → ℕ)
    (pl : (Σ i : Fin K, Fin (what₂ i)) → Fin N), Function.Injective pl →
    ∀ (P : ∀ i, MvPolynomial (Fin (what₂ i) × WV I) C) (kind : ∀ i, Fin (what₂ i) → Knd d)
      (gr : ∀ i, Fin (what₂ i) → MvPowerSeries (WV I) C),
      ValOf hL (prodAll pl P) (kindAll pl kind) (grAll pl gr) = ∏ i, ValOf hL (P i) (kind i) (gr i)
end Formalism.L2.FormalSeriesBounds


