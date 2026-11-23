-- Prove2me | Definitions.Def_PerishablePricing_Backlog_Supplement_IntegerLNat
-- name    : PerishablePricing_Backlog_Supplement_IntegerLNat
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T06:57:54.955798+00:00
-- url     : https://prove2.me/theorems/2b7e5cbd-020a-4272-b30b-e68c35e446af
-- title:
--   Definition 1, p. 287 — integer L♮-convexity on an effective domain
-- statement:
--   Let $S\subseteq\mathbb Z^{\iota}$ and let $f:S\to\mathbb R$. Its extension is $+\infty$ off $S$. The domain is L♮-convex when both $(u+\alpha e)\wedge v$ and $u\vee(v-\alpha e)$ belong to $S$ for every $u,v\in S$ and integer $\alpha\ge0$. The function is L♮-convex precisely when the domain has that property and
--
--   $$f((u+\alpha e)\wedge v)+f(u\vee(v-\alpha e))\le f(u)+f(v).$$
--
--   L♮-concavity is L♮-convexity of $-f$. The ordered sets $\mathcal V_{n,k}$ and $\mathcal V^+_{n,k}$ impose $s_1\le\cdots\le s_k$ and $0\le s_1\le\cdots\le s_k$, respectively. This supplies the integer carrier of Lemma 4; its real carrier uses the published definition unchanged.
--
--   **Formalization Note** Finite values on an arbitrary effective domain encode every function to $\mathbb R\cup\{+\infty\}$, including the identically infinite function. No subtraction of infinities occurs. Coordinates in `Fin n` are numbered from zero.
-- source:
--   Chen, Pang, Pan, Coordinating Inventory Control and Pricing Strategies for Perishable Products, Oper. Res. 62(2), 2014, https://doi.org/10.1287/opre.2014.1261, Definition 1 and ordered sets, p. 287 (PDF 5)

import Mathlib

namespace PerishablePricing.Backlog.Supplement

/-- Definition 1 over the other carrier allowed on p. 287, namely the integers.
The real version is the published `PerishablePricing.Backlog.LNatConvexOn`. -/
def LNatConvexSetZ {ι : Type*} (S : Set (ι → ℤ)) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, ∀ α : ℤ, 0 ≤ α →
    (u + α • (1 : ι → ℤ)) ⊓ v ∈ S ∧ u ⊔ (v - α • (1 : ι → ℤ)) ∈ S

/-- Finite real values on the effective domain, extended by +∞ outside it. -/
def LNatConvexOnZ {ι : Type*} (S : Set (ι → ℤ)) (f : (ι → ℤ) → ℝ) : Prop :=
  LNatConvexSetZ S ∧
    ∀ u ∈ S, ∀ v ∈ S, ∀ α : ℤ, 0 ≤ α →
      f ((u + α • (1 : ι → ℤ)) ⊓ v) + f (u ⊔ (v - α • (1 : ι → ℤ))) ≤ f u + f v

def LNatConcaveOnZ {ι : Type*} (S : Set (ι → ℤ)) (f : (ι → ℤ) → ℝ) : Prop :=
  LNatConvexOnZ S (-f)

def VZ (n k : ℕ) : Set (Fin n → ℤ) :=
  {s | ∀ i j : Fin n, i ≤ j → (j : ℕ) < k → s i ≤ s j}

def VplusZ (n k : ℕ) : Set (Fin n → ℤ) :=
  {s | s ∈ VZ n k ∧ ∀ i : Fin n, (i : ℕ) < k → 0 ≤ s i}

end PerishablePricing.Backlog.Supplement


