-- Prove2me | Definitions.Def_NSWBetter_IsValidCLP
-- name    : NSWBetter_IsValidCLP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:49:35.131318+00:00
-- url     : https://prove2.me/theorems/a852ba59-9bba-4cea-8867-5a480887facf
-- title:
--   Feasible solution of the configuration LP, constraints (2)–(4)
-- statement:
--   A vector $y=(y_{i,S})_{i\in N,S\subseteq G}$ is a **valid** (feasible) solution of the configuration LP when
--   $$\sum_{S\subseteq G}y_{i,S}=1\ \ \forall i\in N\quad(2),\qquad \sum_{i\in N}\sum_{S\ni g}y_{i,S}=1\ \ \forall g\in G\quad(3),\qquad y_{i,S}\ge0\quad(4).$$
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Section 2.1, p.10, configuration LP (2)–(4)

import Mathlib

namespace NSWBetter

open Classical in
/-- **Feasibility for the configuration LP.**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Section 2.1, p.10, configuration LP: (2) `Σ_(S⊆G) yi,S = 1` for every agent `i`; (3) `Σ_(i∈N) Σ_(S∋g) yi,S = 1` for every good `g`; (4) `yi,S ≥ 0`.

`y i S` is the variable `y_(i,S)`. -/
def IsValidCLP {n m : ℕ} (y : Fin n → Finset (Fin m) → ℝ) : Prop :=
  (∀ i S, 0 ≤ y i S) ∧ (∀ i, ∑ S, y i S = 1) ∧
  ∀ g, ∑ i, ∑ S ∈ Finset.univ.filter (fun S => g ∈ S), y i S = 1

end NSWBetter


