-- Prove2me | Definitions.Def_MartOT_Shadow_ConvergesInM
-- name    : MartOT_Shadow_ConvergesInM
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T00:19:18.008643+00:00
-- url     : https://prove2.me/theorems/d7f1f3a8-4d1d-44fe-971c-c5577c5d7776
-- title:
--   §2.1, p. 10 — weak convergence in 𝓜: weak convergence plus convergence of ∫|x|
-- statement:
--   Let $\mathcal M$ be the set of finite Borel measures on $\mathbb R$ with finite first moment. A sequence $(\nu_n)_{n\in\mathbb N}$ of elements of $\mathcal M$ **converges weakly in $\mathcal M$** to $\nu\in\mathcal M$ if
--
--   1. $(\nu_n)_n$ converges weakly in the usual sense: for every continuous bounded $f:\mathbb R\to\mathbb R$,
--   $$\int f\,d\nu_n\longrightarrow\int f\,d\nu ;$$
--   2. the first absolute moments converge: $\int|x|\,d\nu_n(x)\to\int|x|\,d\nu(x)$.
--
--   Equivalently, test functions growing at most linearly at $\pm\infty$ are added to the continuous bounded ones. This is the topology on $\mathcal M$ used for the approximation arguments of the paper (Lemma 2.9, Proposition 4.2, Proposition 4.15).
--
--   **Formalization Note** The two conditions are encoded literally, with Bochner integrals, and the membership of every $\nu_n$ and of $\nu$ in $\mathcal M$ is part of the definition, so all integrals involved are finite. Mathlib's topology on probability measures is not used because the measures here have arbitrary finite mass.
-- source:
--   arXiv:1208.1509v2, §2.1, p. 10

import Mathlib
import Definitions.Def_MartOT_Var_Setting

namespace MartOT.Shadow

open MeasureTheory Filter Topology BoundedContinuousFunction

/-- **Convergence weakly in `𝓜`** (§2.1, p. 10): a sequence `(νₙ)` of elements of `𝓜` converges weakly
in `𝓜` to `ν ∈ 𝓜` if (1) `∫ f dνₙ → ∫ f dν` for every continuous bounded `f`, and
(2) `∫ |x| dνₙ → ∫ |x| dν`. -/
def ConvergesInM (νs : ℕ → Measure ℝ) (ν : Measure ℝ) : Prop :=
  (∀ n, MartOT.Var.InM (νs n)) ∧ MartOT.Var.InM ν ∧
    (∀ f : ℝ →ᵇ ℝ, Tendsto (fun n => ∫ x, f x ∂(νs n)) atTop (𝓝 (∫ x, f x ∂ν))) ∧
    Tendsto (fun n => ∫ x, |x| ∂(νs n)) atTop (𝓝 (∫ x, |x| ∂ν))

end MartOT.Shadow


