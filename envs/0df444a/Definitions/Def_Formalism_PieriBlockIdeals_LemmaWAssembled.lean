-- Prove2me | Definitions.Def_Formalism_PieriBlockIdeals_LemmaWAssembled
-- name    : Formalism_PieriBlockIdeals_LemmaWAssembled
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:07:42.680269+00:00
-- url     : https://prove2.me/theorems/4bdcb98f-4cf3-48f0-af8f-633c94e13fa5
-- title:
--   Lemma WAssembled
-- statement:
--   Definitions and structural lemmas for Lemma WAssembled, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/LemmaWAssembled.lean

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLW
import Definitions.Def_Formalism_PieriBlockIdeals_WEChain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
namespace Formalism.CohomologicalDescent
structure WData (ι : Type) (t n : ℕ) (F : Type) [Field F] where
  a : F
  Θ : ι → Matrix (Fin n) (Fin n) F
  Φ : ι → Matrix (Fin n) (Fin n) (PowerSeries F)
  b : Fin n → ℕ
  pos : Fin t → Fin n
def WProps {ι : Type} [Fintype ι] {t n : ℕ} {F : Type} [Field F] (W : WData ι t n F)
    (σ : Equiv.Perm ι) (l : ℕ) (U' : ι → Fin n → ℤ) (bot : ι → ℤ) (kap : ι → Fin t → ℤ)
    (c : ι → ℕ) : Prop :=
  W.a ≠ 0 ∧ Function.Injective W.pos ∧ (∀ s j, W.b j = W.b (W.pos s) → j = W.pos s) ∧
  (∀ i, (W.Θ i).BlockTriangular W.b) ∧
  (∀ i, (W.Θ i).charpoly = ∏ u, (Polynomial.X - Polynomial.C (-W.a * ((U' i u : ℤ) : F)))) ∧
  (∀ i s, W.Θ i (W.pos s) (W.pos s) = -W.a * ((bot i + ((s : ℕ) : ℤ) - kap i s : ℤ) : F)) ∧
  (∀ i, (W.Φ i).BlockTriangular W.b) ∧
  (∀ i s, ∃ u : (PowerSeries F)ˣ, W.Φ i (W.pos s) (W.pos s) =
    (u : PowerSeries F) *
      PowerSeries.X ^ ((l : ℤ) * kap (σ i) s + (bot i + ((s : ℕ) : ℤ)) - kap i s).toNat) ∧
  (∀ i, (PowerSeries.X : PowerSeries F) ^ c i ∣ ((W.Φ i).submatrix W.pos W.pos).det)
def LemmaWAssembled : Prop :=
  ∀ (ι : Type) [Fintype ι] (σ : Equiv.Perm ι) (l h t n : ℕ) (F : Type) [Field F] [CharP F l]
    (W : WData ι t n F) (U' : ι → Fin n → ℤ) (bot : ι → ℤ) (kap : ι → Fin t → ℤ) (c : ι → ℕ),
    l.Prime → WProps W σ l U' bot kap c →
    (∀ i (s : Fin t), 0 ≤ bot i + ((s : ℕ) : ℤ) ∧ bot i + ((s : ℕ) : ℤ) ≤ (h : ℤ)) →
    (∀ i (s : Fin t), 0 ≤ (l : ℤ) * kap (σ i) s + (bot i + ((s : ℕ) : ℤ)) - kap i s ∧
      (l : ℤ) * kap (σ i) s + (bot i + ((s : ℕ) : ℤ)) - kap i s ≤ (h : ℤ)) →
    (∀ i s, ((l : ℤ) - 1) * |kap i s| ≤ (h : ℤ)) ∧
    (∀ i, Multiset.map (fun s : Fin t => ((bot i + ((s : ℕ) : ℤ) - kap i s : ℤ) : ZMod l))
        Finset.univ.val ≤ Multiset.map (fun u => ((U' i u : ℤ) : ZMod l)) Finset.univ.val) ∧
    (∀ i, (c i : ℤ) ≤ ∑ s : Fin t, (bot i + ((s : ℕ) : ℤ) + (l : ℤ) * kap (σ i) s - kap i s))
def WEFull : Prop :=
  ∀ (ι : Type) [Fintype ι] (σ : Equiv.Perm ι) (k j t q l h : ℕ) (F : Type) [Field F] [CharP F l]
    (W : WData ι t (k + j + t + q) F) (U U' : ι → Fin (k + j + t + q) → ℤ) (bot cst : ι → ℤ)
    (kap : ι → Fin t → ℤ) (c : ι → ℕ) (τ : ι),
    l.Prime → t + 2 * (h / (l - 1)) < l →
    WProps W σ l U' bot kap c →
    (∀ i (s : Fin t), 0 ≤ bot i + ((s : ℕ) : ℤ) ∧ bot i + ((s : ℕ) : ℤ) ≤ (h : ℤ)) →
    (∀ i (s : Fin t), 0 ≤ (l : ℤ) * kap (σ i) s + (bot i + ((s : ℕ) : ℤ)) - kap i s ∧
      (l : ℤ) * kap (σ i) s + (bot i + ((s : ℕ) : ℤ)) - kap i s ≤ (h : ℤ)) →
    (∀ i, StrictAnti (U i)) → (∀ i, StrictAnti (U' i)) →
    (∀ i (s : Fin t), ∃ a, U i a = bot i + ((s : ℕ) : ℤ)) →
    (∀ i, (∏ a, (Polynomial.X + Polynomial.C (((U i a + cst i : ℤ)) : F))) =
      ∏ a, (Polynomial.X + Polynomial.C (((U' i a + cst i : ℤ)) : F))) →
    (∀ a, 0 ≤ U τ a) → (∀ a, 0 ≤ U' τ a ∧ U' τ a ≤ (h : ℤ)) → ∑ a, U τ a = ∑ a, U' τ a →
    (∀ a : Fin (k + j + t + q), k + j ≤ (a : ℕ) → (a : ℕ) < k + j + t →
      U τ a = bot τ + ((k + j + t - 1 - (a : ℕ) : ℕ) : ℤ)) →
    (c τ : ℤ) = ∑ a ∈ Finset.univ.filter (fun a : Fin (k + j + t + q) => k + j + q ≤ (a : ℕ)),
      U' τ a →
    ∑ a ∈ Finset.univ.filter (fun a : Fin (k + j + t + q) => (a : ℕ) < k + j), (U τ a - U' τ a) ≤
      (q : ℤ) * h +
        ((l : ℤ) * (mwCount l (bot (σ τ)) t (h / (l - 1)) (Finset.univ.image (U (σ τ))) : ℤ) +
          (mwCount l (bot τ) t (h / (l - 1)) (Finset.univ.image (U τ)) : ℤ)) *
          ((t : ℤ) + 2 * ((h / (l - 1) : ℕ) : ℤ))
end Formalism.CohomologicalDescent


