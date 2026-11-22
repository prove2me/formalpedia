-- Prove2me | Definitions.Def_Formalism_IncomingBounds_IncomingBound
-- name    : Formalism_IncomingBounds_IncomingBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:55:20.946716+00:00
-- url     : https://prove2.me/theorems/e42c3595-79ff-441f-a16e-f87f0cd15166
-- title:
--   Incoming Bound
-- statement:
--   Definitions and structural lemmas for Incoming Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/IncomingBound.lean

import Mathlib
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
namespace Formalism.IncomingBounds
def rho (l : ℕ) : ℝ := 1 / ((l : ℝ) ^ 2 - 1)
def gam (l : ℕ) : ℝ := (l : ℝ) / ((l : ℝ) ^ 2 - 1)
def oddLevels (d : ℕ) : Finset ℕ := (Finset.range d).filter Odd
section LP
variable (l d : ℕ) [NeZero d]
def IsFlow (D : ZMod d → ℝ) (x : ZMod d → ℕ → ℝ) : Prop :=
  (∀ s i, 0 ≤ x s i) ∧
    ∀ s : ZMod d, (∑ i ∈ oddLevels d, (l : ℝ) ^ i * x s i) +
      (∑ i ∈ oddLevels d, x (s - (i : ZMod d)) i) ≤ D s
def flowVal (x : ZMod d → ℕ → ℝ) : ℝ := ∑ s : ZMod d, ∑ i ∈ oddLevels d, x s i
def maxFlow (D : ZMod d → ℝ) : ℝ :=
  sSup {t : ℝ | ∃ x, IsFlow l d D x ∧ flowVal d x = t}
def Fnum (D : ZMod d → ℝ) : ℝ := gam l * (∑ s : ZMod d, D s) - maxFlow l d D
def IsDual (sig : ZMod d → ℝ) : Prop :=
  (∀ s, 0 ≤ sig s ∧ sig s ≤ 1) ∧
    ∀ s : ZMod d, ∀ i ∈ oddLevels d, 1 ≤ (l : ℝ) ^ i * sig s + sig (s + (i : ZMod d))
def IsDualAll (sig : ZMod d → ℝ) : Prop :=
  ∀ s : ZMod d, ∀ i : ℕ, Odd i → 1 ≤ (l : ℝ) ^ i * sig s + sig (s + (i : ZMod d))
def IsOptDual (D sig : ZMod d → ℝ) : Prop :=
  IsDual l d sig ∧ Fnum l d D = ∑ s : ZMod d, D s * (gam l - sig s)
end LP
def Constants : Prop :=
  ∀ l : ℕ, 2 ≤ l →
    HasSum (fun k : ℕ => ((l : ℝ) ^ (2 * k + 1))⁻¹) (gam l) ∧
      rho l + gam l = 1 / ((l : ℝ) - 1)
def ValGain : Prop :=
  ∀ l : ℕ, l.Prime →
    (∀ n : ℕ, 1 ≤ n → 1 / ((l : ℝ) - 1) ≤ (n : ℝ) / ((l : ℝ) - 1) - (padicValNat l n : ℝ)) ∧
      ∀ e : ℕ, rho l ≤ ((l : ℝ) ^ 2) ^ e * rho l - e
def FlowAttained : Prop :=
  ∀ (l d : ℕ) [NeZero d], 3 ≤ l → 2 ≤ d → Even d → ∀ D : ZMod d → ℝ, 0 ≤ D →
    ∃ x, IsFlow l d D x ∧ flowVal d x = maxFlow l d D
def LemmaFa : Prop :=
  ∀ (l d : ℕ) [NeZero d], 3 ≤ l → 2 ≤ d → Even d → ∀ D : ZMod d → ℝ, 0 ≤ D →
    (∃ sig, IsDual l d sig ∧ IsDualAll l d sig ∧
        Fnum l d D = ∑ s : ZMod d, D s * (gam l - sig s)) ∧
      IsGreatest {t : ℝ | ∃ sig, IsDual l d sig ∧ t = ∑ s : ZMod d, D s * (gam l - sig s)}
        (Fnum l d D)
def LemmaFb : Prop :=
  ∀ (l d : ℕ) [NeZero d], 3 ≤ l → 2 ≤ d → Even d →
    (∀ (c : ℝ) (D : ZMod d → ℝ), 0 ≤ c → 0 ≤ D → Fnum l d (c • D) = c * Fnum l d D) ∧
      ConvexOn ℝ {D : ZMod d → ℝ | 0 ≤ D} (Fnum l d) ∧
      ∀ D : ZMod d → ℝ, 0 ≤ D → rho l * (∑ s : ZMod d, D s) ≤ Fnum l d D
def LemmaFc : Prop :=
  ∀ (l d : ℕ) [NeZero d], 3 ≤ l → 2 ≤ d → Even d → ∀ D E sig : ZMod d → ℝ, 0 ≤ D → 0 ≤ E →
    IsOptDual l d D sig →
      Fnum l d D - (∑ s : ZMod d, E s * max (sig s - gam l) 0) ≤ Fnum l d (D + E) ∧
        Fnum l d (D + E) ≤ Fnum l d D + gam l * (∑ s : ZMod d, E s)
def LemmaFd : Prop :=
  ∀ (l d : ℕ) [NeZero d], 3 ≤ l → 2 ≤ d → Even d → ∀ D sig : ZMod d → ℝ, 0 ≤ D →
    IsOptDual l d D sig → ∀ s : ZMod d, 2 / (l : ℝ) ≤ sig s →
      (∀ x, IsFlow l d D x → flowVal d x = maxFlow l d D →
          (∀ i ∈ oddLevels d, x s i = 0) ∧ D s = ∑ i ∈ oddLevels d, x (s - (i : ZMod d)) i) ∧
        D s ≤ ∑ i ∈ oddLevels d, D (s - (i : ZMod d)) / (l : ℝ) ^ i ∧
        (0 < D s → ∃ s' : ZMod d, D s / gam l ≤ D s')
def LemmaFe : Prop :=
  ∀ (l d : ℕ) [NeZero d], 3 ≤ l → 2 ≤ d → Even d → ∀ D : ZMod d → ℝ, 0 ≤ D →
    (∀ s s' : ZMod d, D s' ≤ (l : ℝ) * D s) → Fnum l d D = rho l * (∑ s : ZMod d, D s)
def IncomingBound : Prop :=
  ∀ (l d : ℕ) [NeZero d], 3 ≤ l → 2 ≤ d → Even d → ∀ D sig : ZMod d → ℝ, 0 ≤ D →
    IsOptDual l d D sig →
      (∑ s ∈ Finset.univ.filter (fun s : ZMod d => 2 / (l : ℝ) ≤ sig s), D s) ≤
        (∑ s : ZMod d, D s) / l
def TopRadius : Prop :=
  ∀ (l : ℕ), 2 ≤ l → ∀ (A : ℝ) (cap : ℕ → ℝ) (J : ℕ), 0 ≤ A → (∀ j, 0 ≤ cap j) → Odd J →
    ∃ eps : ℝ, ((l : ℝ) ^ J)⁻¹ ≤ eps ∧
      A * eps + (∑ j ∈ (Finset.range J).filter Odd, cap j * max (1 - (l : ℝ) ^ j * eps) 0) ≤
        (∑ j ∈ (Finset.range J).filter Odd, min (cap j) (A / (l : ℝ) ^ j)) + A / (l : ℝ) ^ J
section TopData
variable (l d : ℕ) [NeZero d] (TT : Finset (ZMod d)) (nu1 nu2 size : ZMod d → ℕ)
def capL (s : ZMod d) : ℕ := if s ∈ TT then nu2 s else nu1 s
def Dl (s : ZMod d) : ℕ := if s ∈ TT then size s - nu1 s else size s
def dTop (s : ZMod d) : ℕ∞ := ⨅ (e : ℕ) (_ : Odd e ∧ s + (e : ZMod d) ∈ TT), (e : ℕ∞)
def Wcap (s : ZMod d) : ℕ :=
  sSup ((fun i : ℕ => capL d TT nu1 nu2 (s - (i : ZMod d))) ''
    {i : ℕ | Odd i ∧ l ^ i ≤ size (s - (i : ZMod d))})
def topTerm (s : ZMod d) : ℝ :=
  ∑' e : ℕ,
    if Odd e ∧ (e : ℕ∞) < dTop d TT s then
      max ((nu1 s : ℝ) / (l : ℝ) ^ e - capL d TT nu1 nu2 (s + (e : ZMod d))) 0
    else if Odd e ∧ dTop d TT s < (e : ℕ∞) then (nu1 s : ℝ) / (l : ℝ) ^ e
    else 0
open Classical in

def baseTerm (s : ZMod d) : ℝ :=
  ∑' e : ℕ,
    if Odd e ∧ ¬ (∃ e0 : ℕ, dTop d TT s = (e0 : ℕ∞) ∧ s + (e : ZMod d) = s + (e0 : ZMod d)) then
      max (((nu1 s : ℝ) - nu2 s) / (l : ℝ) ^ e - capL d TT nu1 nu2 (s + (e : ZMod d))) 0
    else 0
def ThmABound (N0 N1 a : ℕ) (CA vK : ℝ) : Prop :=
  (∑ s ∈ TT, (topTerm l d TT nu1 nu2 s - gam l * (Wcap l d TT nu1 nu2 size s : ℝ))) +
      Fnum l d (fun s => (Dl d TT nu1 size s : ℝ)) -
      CA * ((d : ℝ) * N0 * N1 * (Real.logb l a + 1)) ≤ vK
end TopData
def CorFromThmA : Prop :=
  ∃ C : ℝ, ∀ (l d : ℕ) [NeZero d], 3 ≤ l → 2 ≤ d → Even d →
    ∀ (TT : Finset (ZMod d)) (nu1 nu2 size : ZMod d → ℕ) (N0 N1 a k : ℕ) (c CA vK : ℝ)
      (w E : ZMod d → ℝ),
      (∀ s, nu2 s ≤ nu1 s) → (∀ s, nu1 s + nu2 s ≤ size s) → 3 ≤ k →
      (∀ s, 0 < w s) → (∀ s, 0 ≤ E s ∧ E s ≤ 4 * w s) →
      (∀ s, s ∉ TT → (Dl d TT nu1 size s : ℝ) = ((k : ℝ) - 1) * w s + E s) →
      (∀ s, s ∈ TT → (Dl d TT nu1 size s : ℝ) = ((k : ℝ) - 1) * w s - 2 * w s + E s) →
      (∀ s, (capL d TT nu1 nu2 s : ℝ) ≤ w s + c) →
      ThmABound l d TT nu1 nu2 size N0 N1 a CA vK →
        (∑ s ∈ TT, baseTerm l d TT nu1 nu2 s) + Fnum l d (fun s => ((k : ℝ) - 1) * w s) -
            C * (∑ s : ZMod d, w s) / l -
            gam l * (∑ s ∈ TT, (Wcap l d TT nu1 nu2 size s : ℝ)) -
            CA * ((d : ℝ) * N0 * N1 * (Real.logb l a + 1)) ≤ vK
end Formalism.IncomingBounds


