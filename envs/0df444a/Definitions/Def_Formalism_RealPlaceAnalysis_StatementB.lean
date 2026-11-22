-- Prove2me | Definitions.Def_Formalism_RealPlaceAnalysis_StatementB
-- name    : Formalism_RealPlaceAnalysis_StatementB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:47:58.170213+00:00
-- url     : https://prove2.me/theorems/8acf861e-0036-4557-b249-5288afe02c82
-- title:
--   Statement B
-- statement:
--   Definitions and structural lemmas for Statement B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/StatementB.lean

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
namespace Formalism.REAL
def epow {A : Type*} [Ring A] {n : ℕ} (E : Fin n → Fin n → A) : ℕ → Fin n → Fin n → A
  | 0 => fun a b => if a = b then 1 else 0
  | k + 1 => fun a b => ∑ c, epow E k a c * E c b
def etr {A : Type*} [Ring A] {n : ℕ} (E : Fin n → Fin n → A) (k : ℕ) : A :=
  ∑ a, epow E k a a
def IsHW {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (ν : Fin n → ℂ) (v : V) : Prop :=
  (∀ a, E a a v = ν a • v) ∧ ∀ a b, a < b → E a b v = 0
def lsh {n : ℕ} (ν : Fin n → ℂ) : Fin n → ℂ := fun a => ν a + ((n : ℂ) - 1 - (a : ℂ))
def Amat {n : ℕ} (l : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun a b => if a = b then l a else if a < b then -1 else 0
def Dfac {n : ℕ} (l : Fin n → ℂ) (s : Fin n) : ℂ :=
  ∏ a ∈ univ.erase s, (l s - l a - 1) / (l s - l a)
def vand {n : ℕ} (l : Fin n → ℂ) : ℂ :=
  ∏ a, ∏ b ∈ univ.filter (fun b => a < b), (l a - l b)
def EpowCov : Prop :=
  ∀ (A : Type) [Ring A] (n : ℕ) (E : Fin n → Fin n → A), GlRel E →
    ∀ (k : ℕ) (a b c d : Fin n),
      E c d * epow E k a b - epow E k a b * E c d =
        (if d = a then epow E k c b else 0) - (if b = c then epow E k a d else 0)
def EtrCentral : Prop :=
  ∀ (A : Type) [Ring A] (n : ℕ) (E : Fin n → Fin n → A), GlRel E →
    ∀ (k : ℕ) (c d : Fin n), etr E k * E c d = E c d * etr E k
def UpperKill : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V)
    (ν : Fin n → ℂ) (v : V), GlRel E → IsHW E ν v →
    ∀ (k : ℕ) (a b : Fin n), a < b → epow E k a b v = 0
def HWDiag : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V)
    (ν : Fin n → ℂ) (v : V), GlRel E → IsHW E ν v →
    ∀ (k : ℕ) (a : Fin n),
      epow E (k + 1) a a v =
        lsh ν a • epow E k a a v - ∑ b ∈ univ.filter (fun b => a < b), epow E k b b v
def DiagChar : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V)
    (ν : Fin n → ℂ) (v : V), GlRel E → IsHW E ν v →
    ∀ a : Fin n,
      ∑ i ∈ range (n + 1),
        (∏ s : Fin n, (Polynomial.X - Polynomial.C (lsh ν s))).coeff i • epow E i a a v = 0
def PPGen : Prop :=
  ∀ (n : ℕ) (l : Fin n → ℂ) (u : ℂ), (∀ a, u ≠ l a) →
    ∑ a, ∑ b, ((u • (1 : Matrix (Fin n) (Fin n) ℂ) - Amat l)⁻¹) a b =
      1 - ∏ a, (u - l a - 1) / (u - l a)
def DsVand : Prop :=
  ∀ (n : ℕ) (l : Fin n → ℂ), Function.Injective l →
    ∀ s, Dfac l s = vand (l - Pi.single s 1) / vand l
def DsSum : Prop :=
  ∀ (n : ℕ) (l : Fin n → ℂ), Function.Injective l → ∑ s, Dfac l s = (n : ℂ)
def TrPowHW : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V)
    (ν : Fin n → ℂ) (v : V), GlRel E → IsHW E ν v → Function.Injective (lsh ν) →
    ∀ k : ℕ, etr E k v = (∑ s, Dfac (lsh ν) s * lsh ν s ^ k) • v
end Formalism.REAL


