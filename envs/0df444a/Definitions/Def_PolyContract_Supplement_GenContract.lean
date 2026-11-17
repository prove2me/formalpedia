-- Prove2me | Definitions.Def_PolyContract_Supplement_GenContract
-- name    : PolyContract_Supplement_GenContract
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:58:09.693479+00:00
-- url     : https://prove2.me/theorems/d7142039-b7c6-4bd5-a26c-eacf29376d0f
-- title:
--   Contract instance over a general action set: best response, $U_P$, $\mathrm{OPT}$, share bound, homogeneous costs
-- statement:
--   A **contract instance over a general action set** consists of a finite nonempty ground set $E$, an action set $K\subseteq\mathbb R^E_{\ge0}$, rewards $m\in\mathbb R^E_{\ge0}$ with expected reward $r(x)=m^\top x$, and a cost $c:\mathbb R^E_{\ge0}\to\mathbb R_{\ge0}$ with $c(0)=0$. Under the linear contract with share $\alpha$ the agent's utility is $U_A(x\mid\alpha)=\alpha\,r(x)-c(x)$. The module defines:
--
--   1. a **best response** $x^\star(\alpha)\in\arg\max_{x\in K}U_A(x\mid\alpha)$, and the reward $r(x^\star(\alpha))$ with ties broken in favour of the principal (the largest reward over all best responses);
--   2. the principal's utility $U_P(\alpha)=(1-\alpha)\,r(x^\star(\alpha))$ and $\mathrm{OPT}:=\sup_{\alpha\in[0,1]}U_P(\alpha)$;
--   3. the **attainment assumption** of §2: for every $\alpha\in[0,1]$ a best response exists and the reward attains its maximum over the best responses;
--   4. a **share bound**: a number $\bar\alpha\in[0,1)$ with $\sup_{\alpha\in[0,\bar\alpha]}U_P(\alpha)=\mathrm{OPT}$;
--   5. costs **homogeneous of degree $p>1$**: $c$ continuous and convex on $\mathbb R^E_{\ge0}$ with $c(tx)=t^p c(x)$ for $t>0$.
--
--   These are the objects of the approximation results of §5, which hold beyond polymatroids and quadratic costs.
--
--   **Formalization Note** The standing hypotheses ($E\ne\emptyset$, $K\subseteq\mathbb R^E_{\ge0}$, $m\ge0$, $c\ge0$, $c(0)=0$) are a separate predicate `Valid`; the attainment assumption is the predicate `Attains`, a hypothesis of the theorems that need it. Under it the utilities on $[0,1]$ are bounded, so the real supremum is the supremum.
-- source:
--   Klimm, Lippke, Warode, The Complexity of Continuous Contract Design over Polymatroids, arXiv:2611.04934 (version of November 3, 2026, sha256 18cfc0a5…), §2, pp.5–6 (PDF pp.6–7); §5, p.11 (PDF p.12); §5.1, p.11

import Mathlib

set_option autoImplicit false

namespace PolyContract.Supplement

/-- The nonnegative orthant `ℝ^E_{≥0}`. -/
def orthant (ι : Type) : Set (ι → ℝ) := {x | ∀ e, 0 ≤ x e}

/-- A **contract instance over a general action set** (Klimm, Lippke, Warode, *The Complexity of
Continuous Contract Design over Polymatroids*, arXiv:2611.04934, version of November 3, 2026,
sha256 18cfc0a5…, §2, pp.5–6, and §5, p.11): a ground set `E` (the finite type `ι`), an action
set `K ⊆ ℝ^E_{≥0}`, rewards `m ∈ ℝ^E_{≥0}` with expected reward `r(x) = m⊤x`, and a cost
`c : ℝ^E_{≥0} → ℝ_{≥0}` with `c(0) = 0`.

**Formalization Note** The structure carries only the data; the standing hypotheses of §2 are the
predicate `GenContract.Valid`. The cost is a function on all of `ℝ^E`, of which only the values on
the orthant matter. -/
structure GenContract (ι : Type) where
  /-- The action set `K`. -/
  K : Set (ι → ℝ)
  /-- The rewards `m_e`. -/
  m : ι → ℝ
  /-- The cost function `c`. -/
  c : (ι → ℝ) → ℝ

namespace GenContract

variable {ι : Type} [Fintype ι]

/-- The standing hypotheses of §2 (arXiv:2611.04934, p.5): the ground set is nonempty,
`K ⊆ ℝ^E_{≥0}`, `m ≥ 0`, `c ≥ 0` on `ℝ^E_{≥0}`, and `c(0) = 0`. -/
def Valid (I : GenContract ι) : Prop :=
  Nonempty ι ∧ I.K ⊆ orthant ι ∧ (∀ e, 0 ≤ I.m e) ∧ (∀ x ∈ orthant ι, 0 ≤ I.c x) ∧ I.c 0 = 0

/-- The expected reward `r(x) := m⊤x` (arXiv:2611.04934, §2, p.5). -/
def reward (I : GenContract ι) (x : ι → ℝ) : ℝ := ∑ e, I.m e * x e

/-- The agent's utility `U_A(x | α) := α r(x) − c(x)` (arXiv:2611.04934, §2, p.5). -/
def agentUtility (I : GenContract ι) (α : ℝ) (x : ι → ℝ) : ℝ := α * I.reward x - I.c x

/-- `x` is a **best response** to the share `α`: `x ∈ arg max_{x ∈ K} U_A(x | α)`
(arXiv:2611.04934, §2, p.5). -/
def IsBestResponse (I : GenContract ι) (α : ℝ) (x : ι → ℝ) : Prop :=
  x ∈ I.K ∧ ∀ y ∈ I.K, I.agentUtility α y ≤ I.agentUtility α x

/-- The reward `r(x⋆(α))` under the best response with ties broken in favour of the principal
(arXiv:2611.04934, §2, pp.5–6): the largest reward over the set of best responses. -/
noncomputable def brReward (I : GenContract ι) (α : ℝ) : ℝ :=
  sSup (I.reward '' {x | I.IsBestResponse α x})

/-- The principal's utility `U_P(α) := (1 − α) r(x⋆(α))` (arXiv:2611.04934, §2, pp.5–6). -/
noncomputable def principalUtility (I : GenContract ι) (α : ℝ) : ℝ := (1 - α) * I.brReward α

/-- The attainment assumption of §2 (arXiv:2611.04934, pp.5–6): "We assume that this maximum is
attained and, when using this tie-breaking rule, that the reward attains its maximum over the set
of best responses", for every share `α ∈ [0, 1]`. -/
def Attains (I : GenContract ι) : Prop :=
  ∀ α ∈ Set.Icc (0 : ℝ) 1, ∃ x, I.IsBestResponse α x ∧ ∀ y, I.IsBestResponse α y → I.reward y ≤ I.reward x

/-- `OPT := sup_{α ∈ [0,1]} U_P(α)` (arXiv:2611.04934, §5, p.11).

**Formalization Note** Under `Attains` the utilities on `[0, 1]` are bounded (the reward under the
best response is nondecreasing in the share and nonnegative), so the real `sSup` is the supremum. -/
noncomputable def OPT (I : GenContract ι) : ℝ := sSup (I.principalUtility '' Set.Icc 0 1)

/-- `ᾱ` is a **share bound** (arXiv:2611.04934, §5, p.11): "a number `ᾱ ∈ [0, 1)` such that
`sup_{α ∈ [0, ᾱ]} U_P(α) = OPT`". -/
def IsShareBound (I : GenContract ι) (ᾱ : ℝ) : Prop :=
  ᾱ ∈ Set.Ico (0 : ℝ) 1 ∧ sSup (I.principalUtility '' Set.Icc 0 ᾱ) = I.OPT

/-- The cost is **homogeneous of degree `p > 1`** (arXiv:2611.04934, §5.1, p.11):
"`c : ℝ^E_{≥0} → ℝ_{≥0}` is continuous and convex and `c(tx) = t^p c(x)` for `t > 0`".

**Formalization Note** Continuity, convexity and homogeneity are required on the orthant, the
domain of `c` in the paper; nonnegativity of `c` there is part of `Valid`. -/
def IsHomogeneousCost (I : GenContract ι) (p : ℝ) : Prop :=
  1 < p ∧ ContinuousOn I.c (orthant ι) ∧ ConvexOn ℝ (orthant ι) I.c ∧
    ∀ t : ℝ, 0 < t → ∀ x ∈ orthant ι, I.c (t • x) = t ^ p * I.c x

end GenContract

end PolyContract.Supplement


