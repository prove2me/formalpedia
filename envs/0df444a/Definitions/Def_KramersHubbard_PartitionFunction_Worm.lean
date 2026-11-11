-- Prove2me | Definitions.Def_KramersHubbard_PartitionFunction_Worm
-- name    : KramersHubbard_PartitionFunction_Worm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:05:49.935402+00:00
-- url     : https://prove2.me/theorems/15378106-8b1c-4e5b-8edd-f463db17f6cc
-- title:
--   The explicit determinantal worm chain
-- statement:
--   An ambient configuration is an equal-size pair $s=(A,B)$ of block-index sets. Its unnormalized complex coefficient and normalized coefficient are
--
--   $$w_\lambda(s)=\lambda^{|A\setminus B|}\det G[A,B],\qquad\pi_\lambda(s)=w_\lambda(s)/\sum_tw_\lambda(t).$$
--
--   The chain uses exactly the nonzero-weight support, which equals positive support on the source inputs. It stays put with probability $1/2$; otherwise it uniformly proposes deleting a row of $A$ or adding a column outside $B$. The proposal is accepted with probability $1$ at a defect in $A\setminus B$, and with probability $\lambda$ otherwise. A heat-bath restoration adds a row or deletes a column, with weights equal to determinants without an additional tilt. The kernel sums every possible proposal, including rejections and coincident self-loops. Generic stochasticity, detailed balance, stationarity and the real Poincaré inequality are separate predicates, not assumptions bundled into the model. Complex coefficients are never replaced by absolute values or real parts in the kernel definitions.
-- source:
--   Chaithanya Rayudu, Jun Takahashi, Ojas Parekh, Andrew Zhao, STOC 2027 submission #1325 (October 2026), Efficient classical simulation of Fermi-Hubbard models with Kramers symmetry, Eqs.(36), (40), Section 4.3, pp.16-17; Proposition 8, pp.20-21; printed page = 1-based PDF page. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1325.pdf; PDF SHA-256 e3fd3fa7390d8ff9f0f1e2ee07e6ebc5b8d7304e26be9e76959d9587f4564eae. Canonical submitted artifact, citation_basis: published; title-page date November 3, 2026; no assertion of conference acceptance.

import Definitions.Def_KramersHubbard_PartitionFunction_Green

noncomputable section

attribute [local instance] Classical.propDecidable
open scoped BigOperators
open Matrix
namespace KramersHubbard.PartitionFunction

/-- Equal-size pairs; zero-weight configurations are retained in the ambient space. -/
abbrev Configuration (p : ℕ) :=
  {s : Finset (Fin p) × Finset (Fin p) // s.1.card = s.2.card}

/-- Starting configuration of Section 4.3. -/
def emptyConfiguration (p : ℕ) : Configuration p := ⟨(∅, ∅), rfl⟩

/-- Eq.(41), with the zero-coupling branch required by the corrected threshold. -/
def pairingParameter {N r} (D : Data N r) (β : ℝ) (M : ℕ) : ℝ :=
  let S := ∑ i, Real.sqrt (D.U i)
  if S = 0 then 1/2 else
    min (1/2) (Real.exp (-delta β M * ∑ i, D.U i) / (8 * M * β * S^2))

/-- Unnormalized Eq.(36), still complex; no absolute value or real-part projection. -/
def wormWeight {p} (G : Matrix (Fin p × Fin 2) (Fin p × Fin 2) ℂ)
    (lam : ℝ) (s : Configuration p) : ℂ :=
  (lam : ℂ) ^ (s.val.1 \ s.val.2).card * blockDet G s.val.1 s.val.2

def wormNormalizer {p} (G : Matrix (Fin p × Fin 2) (Fin p × Fin 2) ℂ)
    (lam : ℝ) : ℂ := ∑ s : Configuration p, wormWeight G lam s

def wormLaw {p} (G : Matrix (Fin p × Fin 2) (Fin p × Fin 2) ℂ)
    (lam : ℝ) (s : Configuration p) : ℂ :=
  wormWeight G lam s / wormNormalizer G lam

/-- Exactly all nonzero weights; on the source's inputs these are exactly positive weights. -/
abbrev WormSupport {p} (G : Matrix (Fin p × Fin 2) (Fin p × Fin 2) ℂ) (lam : ℝ) :=
  {s : Configuration p // wormWeight G lam s ≠ 0}

def validMass {p} (G : Matrix (Fin p × Fin 2) (Fin p × Fin 2) ℂ) (lam : ℝ) : ℂ :=
  ∑ s : Configuration p, if s.val.1 = s.val.2 then wormLaw G lam s else 0

/-- A down move: false deletes a row, true adds a column. -/
def downAllowed {p} (s : Configuration p) (c : Fin p × Bool) : Prop :=
  if c.2 then c.1 ∉ s.val.2 else c.1 ∈ s.val.1

def downState {p} (s : Configuration p) (c : Fin p × Bool) :
    Finset (Fin p) × Finset (Fin p) :=
  if c.2 then (s.val.1, insert c.1 s.val.2) else (s.val.1.erase c.1, s.val.2)

def restores {p} (u : Finset (Fin p) × Finset (Fin p)) (s : Configuration p) : Prop :=
  (∃ k, k ∉ u.1 ∧ s.val = (insert k u.1, u.2)) ∨
  (∃ k, k ∈ u.2 ∧ s.val = (u.1, u.2.erase k))

/-- Heat-bath restoration has determinant weights, with no additional lambda tilt. -/
def restoreDenominator {p} (G : Matrix (Fin p × Fin 2) (Fin p × Fin 2) ℂ)
    (u : Finset (Fin p) × Finset (Fin p)) : ℂ :=
  ∑ s : Configuration p, if restores u s then blockDet G s.val.1 s.val.2 else 0

def restoreProbability {p} (G : Matrix (Fin p × Fin 2) (Fin p × Fin 2) ℂ)
    (u : Finset (Fin p) × Finset (Fin p)) (s : Configuration p) : ℂ :=
  if restores u s then blockDet G s.val.1 s.val.2 / restoreDenominator G u else 0

/-- Explicit lazy kernel; sums count coincident outcomes and every rejected move. -/
def wormKernel {p} (G : Matrix (Fin p × Fin 2) (Fin p × Fin 2) ℂ)
    (lam : ℝ) (s t : WormSupport G lam) : ℂ :=
  (if s = t then 1/2 else 0) + (1 / (2 * (p : ℂ))) *
    ∑ c : Fin p × Bool, if downAllowed s.val c then
      let a : ℂ := if c.1 ∈ s.val.val.1 \ s.val.val.2 then 1 else (lam : ℂ)
      (1-a) * (if s = t then 1 else 0) +
        a * restoreProbability G (downState s.val c) t.val
    else 0

/-- Generic finite stochasticity, expressed without building it into a data structure. -/
def Stochastic {S : Type*} [Fintype S] (P : S → S → ℂ) : Prop :=
  (∀ s t, ∃ a : ℝ, 0 ≤ a ∧ P s t = (a : ℂ)) ∧ ∀ s, ∑ t, P s t = 1

def DetailedBalance {S : Type*} (pi : S → ℂ) (P : S → S → ℂ) : Prop :=
  ∀ s t, pi s * P s t = pi t * P t s

def Stationary {S : Type*} [Fintype S] (pi : S → ℂ) (P : S → S → ℂ) : Prop :=
  ∀ t, ∑ s, pi s * P s t = pi t

/-- Gap lower bound in its Poincare form. On a singleton variance is zero and the
    conventional gap is 1. Reality of both sides is part of the assertion. -/
def PoincareBound {S : Type*} [Fintype S] (pi : S → ℂ) (P : S → S → ℂ) (c : ℝ) : Prop :=
  ∀ f : S → ℝ, ∃ E V : ℝ,
    (1/2 : ℂ) * (∑ s, ∑ t, pi s * P s t * ((f s - f t : ℝ) : ℂ)^2) = (E : ℂ) ∧
    (∑ s, pi s * (f s : ℂ)^2) - (∑ s, pi s * (f s : ℂ))^2 = (V : ℂ) ∧
    0 ≤ V ∧ c * V ≤ E

/-- Singleton support has gap 1; for larger support use the Poincare inequality. -/
def GapAtLeast {S : Type*} [Fintype S] (pi : S → ℂ) (P : S → S → ℂ) (c : ℝ) : Prop :=
  (Fintype.card S ≤ 1 → c ≤ 1) ∧ PoincareBound pi P c

end KramersHubbard.PartitionFunction


