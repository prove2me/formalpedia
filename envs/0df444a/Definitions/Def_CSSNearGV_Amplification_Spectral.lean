-- Prove2me | Definitions.Def_CSSNearGV_Amplification_Spectral
-- name    : CSSNearGV_Amplification_Spectral
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T21:16:06.589196+00:00
-- url     : https://prove2.me/theorems/454557a7-4df3-4bc6-966e-483ade655c6f
-- title:
--   Entropy, feasible spectral recurrences and thresholds
-- statement:
--   Write $h$ for binary entropy in bits, with $0\log 0=0$. Define the parity shape $\varphi$, transition exponents $f_A,f_D$, and the spectral recurrences exactly on their feasible domains. Weighted entropy uses its continuous value at a zero coefficient. In particular, $f_A(1,1/2)=0$.
--
--   The GV point is the root of $h(t)=1/s$ on $[0,1/2]$, encoded by the infimum of that root set. The zero threshold is
--   $$\delta^{(m)}=\sup\{\delta\in[0,1/2):r_A^{(m)}(\gamma)\le0\text{ for every }0\le\gamma\le\delta\}.$$
--
--   The associated theorem items establish the root property, attainment of full feasible maxima and attainment of the zero threshold. Restricted maxima use extended reals, with the empty maximum equal to $-\infty$. This avoids assigning an artificial real value to an empty restricted domain. The piecewise comparison shape $g$ uses $\lambda_\gamma=2\gamma(1-\gamma)$.
-- source:
--   Rachel Yun Zhang, Linear-Time Encodable Quantum Codes near the CSS GV Bound, STOC 2027 submission #1164 (October 2026), Definitions 1.2 and 3.1–3.4; Section 5.1, printed pp.1,9–11,16 / PDF 3,11–13,18

import Mathlib
import Definitions.Def_WildeQIT_binaryEntropy

noncomputable section

namespace CSSNearGV.Amplification

abbrev entropy := WildeQIT.binaryEntropy

def phi (s : ℕ) (γ : ℝ) : ℝ :=
  min (entropy γ + (1 / (s : ℝ)) * Real.logb 2 ((1 + (1 - 2 * γ) ^ s) / 2))
    (Real.logb 2 (s - 1 : ℝ) / 2 * min γ (1 - γ) + entropy γ / 2)

def domainA (α β : ℝ) : Prop :=
  0 ≤ α ∧ α ≤ 1 ∧ α / 2 ≤ β ∧ β ≤ 1 - α / 2

def domainD (α β : ℝ) : Prop :=
  0 ≤ α ∧ α ≤ 1 ∧ 0 ≤ β ∧ β ≤ min (2 * α) (2 * (1 - α))

/-- Perspective entropy, including its continuous zero-weight boundary value. -/
def weightedEntropy (t u : ℝ) : ℝ := if t = 0 then 0 else t * entropy (u / t)

def fA (α β : ℝ) : ℝ := α - entropy β + weightedEntropy (1 - α) (β - α / 2)
def fD (α β : ℝ) : ℝ := weightedEntropy (1 - α) (β / 2) +
  weightedEntropy α (β / 2) - entropy α

def domainPair (ad : Bool) (α β γ : ℝ) : Prop :=
  if ad then domainA α β ∧ domainD β γ else domainD α β ∧ domainA β γ

def fPair (ad : Bool) (α β γ : ℝ) : ℝ :=
  if ad then fA α β + fD β γ else fD α β + fA β γ

/-- Suprema are taken only over the compact feasible transition domains. -/
def shapePair (s : ℕ) (ad : Bool) : ℕ → ℝ → ℝ
  | 0 => phi s
  | m + 1 => fun γ => sSup {v | ∃ α β, domainPair ad α β γ ∧ v = shapePair s ad m α + fPair ad α β γ}

def shapeA (s : ℕ) : ℕ → ℝ → ℝ
  | 0 => phi s
  | m + 1 => fun γ => sSup {v | ∃ α, domainA α γ ∧ v = shapeA s m α + fA α γ}

def zeroInterval (s m : ℕ) : Set ℝ :=
  {δ | 0 ≤ δ ∧ δ < 1 / 2 ∧ ∀ γ ∈ Set.Icc (0 : ℝ) δ, shapeA s m γ ≤ 0}

def delta (s m : ℕ) : ℝ := sSup (zeroInterval s m)

def gv (s : ℕ) : ℝ := sInf {δ | δ ∈ Set.Icc (0 : ℝ) (1 / 2) ∧ entropy δ = 1 / (s : ℝ)}

def lambda (γ : ℝ) : ℝ := 2 * γ * (1 - γ)

def g (α γ : ℝ) : ℝ :=
  if α ≤ lambda γ then fA α γ
  else if α ≤ 1 - lambda γ then entropy γ - entropy α
  else fA (1 - α) γ

/-- The empty restricted maximum is -infinity, never the real sSup default zero. -/
def restrictedA (s m : ℕ) (τ γ : ℝ) : EReal :=
  sSup {v | ∃ α, domainA α γ ∧ τ ≤ α ∧ α ≤ 1 - τ ∧
    v = ((shapeA s (m - 1) α + fA α γ : ℝ) : EReal)}

def restrictedPair (s m : ℕ) (ad : Bool) (τ γ : ℝ) : EReal :=
  sSup {v | ∃ α β, domainPair ad α β γ ∧ τ ≤ α ∧ α ≤ 1 - τ ∧
    v = ((shapePair s ad (m - 1) α + fPair ad α β γ : ℝ) : EReal)}

def comparisonMax (s m : ℕ) (ad : Bool) (τ γ : ℝ) : EReal :=
  sSup {v | ∃ α ∈ Set.Icc τ (1 - τ),
    v = ((shapePair s ad (m - 1) α + g α γ : ℝ) : EReal)}

def Symmetric (f : ℝ → ℝ) : Prop := ∀ x ∈ Set.Icc (0 : ℝ) 1, f (1 - x) = f x

def SpectralProperties (f : ℝ → ℝ) : Prop :=
  (∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f x) ∧ Symmetric f ∧
  MonotoneOn f (Set.Icc 0 (1 / 2)) ∧
  Symmetric (fun x => f x - entropy x) ∧
  AntitoneOn (fun x => f x - entropy x) (Set.Icc 0 (1 / 2))

end CSSNearGV.Amplification


