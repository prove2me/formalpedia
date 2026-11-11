-- Prove2me | Definitions.Def_OrderedSearchExact_Exact_Packets
-- name    : OrderedSearchExact_Exact_Packets
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:04:16.168292+00:00
-- url     : https://prove2.me/theorems/e02b4f9b-1f38-4491-909a-fd5369186e54
-- title:
--   Hyperbolic family and continuous packets with endpoint rates
-- statement:
--   Rates range over the extended nonnegative real line $[0,\infty]$. For $1\le j<n$ and $0<\lambda<\infty$ the three coefficient vectors are
--
--   $$g_{\lambda,n}(j)=\frac{\sinh(\lambda(1-j/n))}{\sinh\lambda},\quad s_{\lambda,n}(j)=\frac{\cosh(\lambda(1/2-j/n))}{2\cosh(\lambda/2)},\quad a_{\lambda,n}(j)=\frac{\sinh(\lambda(1/2-j/n))}{2\sinh(\lambda/2)}.$$
--
--   At zero their entries are respectively $1-j/n$, $1/2$, and $1/2-j/n$; at infinity all entries vanish. A density $h$ is measurable, nonnegative almost everywhere, integrable with integral one, and zero almost everywhere outside some compact set. Expectation is Lebesgue integration against $h$. The packet coefficients are the expectations of $s_{\alpha e^Y,n}$ and $a_{\alpha e^Y,n}$, and the hybrid is their sum at possibly different centers. Almost-sure assertions use the law with density $h$.
--
--   These deterministic integrals allow arbitrary compactly supported densities, including nonsmooth and noneven densities. No finite-mixture restriction or random sampling by the eventual query algorithm is introduced.
-- source:
--   Joseph Carolan, Andrew Childs, STOC 2027 submission #1443 (October 2026), Definitions 4.1, 4.3; (13)–(15), p.13–14 (PDF p.13–14); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1443.pdf; sha256 8bb6cbb4037a439039875fd77a9f212e2c0f90a6e87f0c4c690230223813da44

import Definitions.Def_OrderedSearchExact_Exact_Laurent

open MeasureTheory

open Classical

namespace OrderedSearchExact.Exact

abbrev Rate := ENNReal

/-- The standing density convention of p.14, with no smoothness or evenness assumption. -/
def IsDensity (h : ℝ → ℝ) : Prop :=
  Measurable h ∧ (∀ᵐ y, 0 ≤ h y) ∧ Integrable h ∧ (∫ y, h y) = 1 ∧
    ∃ K : Set ℝ, IsCompact K ∧ ∀ᵐ y, y ∉ K → h y = 0

def AlmostSure (h : ℝ → ℝ) (P : ℝ → Prop) : Prop :=
  ∀ᵐ y, h y ≠ 0 → P y

noncomputable def expectation (h f : ℝ → ℝ) : ℝ := ∫ y, h y * f y

/-- Positive scale multiplication is valid also at the genuine endpoints 0 and ∞. -/
noncomputable def physicalRate (α : Rate) (y : ℝ) : Rate :=
  α * ENNReal.ofReal (Real.exp y)

noncomputable def g (n : ℕ) (lam : Rate) : Coeff n := fun i =>
  if lam = ⊤ then 0 else if lam = 0 then fejer n i else
    Real.sinh (lam.toReal * (1 - (i.val + 1 : ℕ) / (n : ℝ))) / Real.sinh lam.toReal

noncomputable def s (n : ℕ) (lam : Rate) : Coeff n := fun i =>
  if lam = ⊤ then 0 else if lam = 0 then 1 / 2 else
    Real.cosh (lam.toReal * (1 / 2 - (i.val + 1 : ℕ) / (n : ℝ))) /
      (2 * Real.cosh (lam.toReal / 2))

noncomputable def a (n : ℕ) (lam : Rate) : Coeff n := fun i =>
  if lam = ⊤ then 0 else if lam = 0 then 1 / 2 - (i.val + 1 : ℕ) / (n : ℝ) else
    Real.sinh (lam.toReal * (1 / 2 - (i.val + 1 : ℕ) / (n : ℝ))) /
      (2 * Real.sinh (lam.toReal / 2))

noncomputable def packetS (n : ℕ) (h : ℝ → ℝ) (α : Rate) : Coeff n :=
  fun i => expectation h (fun y => s n (physicalRate α y) i)

noncomputable def packetA (n : ℕ) (h : ℝ → ℝ) (α : Rate) : Coeff n :=
  fun i => expectation h (fun y => a n (physicalRate α y) i)

noncomputable def hybrid (n : ℕ) (h : ℝ → ℝ) (α β : Rate) : Coeff n :=
  packetS n h α + packetA n h β

end OrderedSearchExact.Exact


