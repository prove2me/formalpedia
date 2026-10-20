-- Prove2me | Definitions.Def_AgencyPassThrough_Pricing_Model
-- name    : AgencyPassThrough_Pricing_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T02:20:40.008979+00:00
-- url     : https://prove2.me/theorems/2158c395-8ae0-4e85-9f92-e2023e918ec0
-- title:
--   §3–§5 — symmetric demand, conduct parameters, equilibrium equations, profits, and K^B
-- statement:
--   Let $D$ be an open interval of positive retail prices and let $q(p)$ be the common demand for one product when all products have price $p$. Write $\lambda(p)=-q(p)/q'(p)$. The standing conditions require positive, decreasing, three-times continuously differentiable demand, $\lambda'(p)<1$, $[\lambda(p)(2-\lambda'(p))]'<1$, and $p\lambda'(p)\leq\lambda(p)$ throughout $D$.
--
--   For $n\geq2$ products, aggregate diversion ratio $\epsilon$, own-brand pass-through $a$, and cross-brand pass-through $b$, the supplier conduct parameters are
--
--   $$\theta^W=\frac{(1-\epsilon)[a+(n-1)b]}{a-\epsilon b},\qquad \theta^B=1-\epsilon.$$
--
--   The wholesale and agency equilibrium price predicates record the two equations of Lemma 1 after setting the e-tailer's unit cost to zero. The associated wholesale price $w^W=p^W-\lambda(p^W)$ and agency commission $\alpha^B=c_s/[p^B-\theta^B\lambda(p^B)]$ determine both parties' profits from the original contract objectives. The threshold $K^B$ and auxiliary curves $\dot\pi$ and $\tilde\pi$ follow §5 and its proof.
--
--   These definitions provide one shared model for every statement in the mission. They record price membership in $D$ and a positive agency commission denominator wherever the equilibrium equation is invoked.
--
--   **Formalization Note** The original $n$-product game is represented by its symmetric-price demand and Lemma 1 equilibrium equations. The demand smoothness, positive demand, and positive agency denominator are explicit regularity conditions.
-- source:
--   Hu, Zheng & Pan, Agency or Wholesale? The Role of Retail Pass-Through, SSRN preprint 3724934 (2021 revision, PDF sha256 1ab91ed8…), p. 7–13, §§3.1–5, A1–A4, Lemma 1, Proposition 2

import Mathlib

namespace AgencyPassThrough.Pricing

/-- Symmetric-price demand sensitivity, §3.1, p. 7. -/
noncomputable def lam (q : ℝ → ℝ) (p : ℝ) : ℝ := -(q p) / deriv q p

/-- Standing demand conditions A1, A3 and A4 on the positive open price interval.
The smoothness and positive-demand clauses make all derivatives and divisions meaningful. -/
structure DemandStanding (q : ℝ → ℝ) (D : Set ℝ) : Prop where
  isOpen : IsOpen D
  ordConnected : D.OrdConnected
  pos : D ⊆ Set.Ioi 0
  smooth : ContDiffOn ℝ 3 q D
  q_pos : ∀ p ∈ D, 0 < q p
  A1 : ∀ p ∈ D, deriv q p < 0
  A3_lam : ∀ p ∈ D, deriv (lam q) p < 1
  A3_lam2 : ∀ p ∈ D,
    deriv (fun x => lam q x * (2 - deriv (lam q) x)) p < 1
  A4 : ∀ p ∈ D, p * deriv (lam q) p ≤ lam q p

/-- Wholesale supplier conduct parameter from the own- and cross-brand pass-through rates. -/
noncomputable def thetaW (n : ℕ) (eps a b : ℝ) : ℝ :=
  (1 - eps) * (a + ((n : ℝ) - 1) * b) / (a - eps * b)

/-- Agency supplier conduct parameter. -/
def thetaB (eps : ℝ) : ℝ := 1 - eps

/-- Wholesale part of Lemma 1 with the e-tailer's unit cost normalized to zero. -/
def IsWholesaleEq (q : ℝ → ℝ) (D : Set ℝ) (cs θW pW : ℝ) : Prop :=
  pW ∈ D ∧ pW - cs = lam q pW + θW * lam q pW * (1 - deriv (lam q) pW)

/-- Agency part of Lemma 1 with the e-tailer's unit cost normalized to zero. -/
def IsAgencyEq (q : ℝ → ℝ) (D : Set ℝ) (cs θB pB : ℝ) : Prop :=
  pB ∈ D ∧ 0 < pB - θB * lam q pB ∧
    pB - cs = lam q pB + cs * θB * lam q pB *
      (((1 - θB) * lam q pB + pB * (1 - deriv (lam q) pB)) /
        (pB - θB * lam q pB) ^ 2)

/-- Equilibrium wholesale price, Lemma 1(i). -/
noncomputable def wW (q : ℝ → ℝ) (pW : ℝ) : ℝ := pW - lam q pW

/-- Equilibrium agency commission, Lemma 1(ii). -/
noncomputable def alphaB (q : ℝ → ℝ) (cs θB pB : ℝ) : ℝ :=
  cs / (pB - θB * lam q pB)

/-- E-tailer wholesale profit from the §3.2 objective at symmetric prices. -/
noncomputable def piWr (n : ℕ) (q : ℝ → ℝ) (pW : ℝ) : ℝ :=
  (n : ℝ) * (pW - wW q pW) * q pW

/-- Each supplier's wholesale profit from the §3.2 objective. -/
noncomputable def piWi (q : ℝ → ℝ) (cs pW : ℝ) : ℝ :=
  (wW q pW - cs) * q pW

/-- E-tailer agency profit from the §3.2 objective at symmetric prices. -/
noncomputable def piBr (n : ℕ) (q : ℝ → ℝ) (cs θB pB : ℝ) : ℝ :=
  (n : ℝ) * ((1 - alphaB q cs θB pB) * pB) * q pB

/-- Each supplier's agency profit from the §3.2 objective. -/
noncomputable def piBi (q : ℝ → ℝ) (cs θB pB : ℝ) : ℝ :=
  (alphaB q cs θB pB * pB - cs) * q pB

/-- The threshold K^B in §5, p. 13. -/
noncomputable def KB (q : ℝ → ℝ) (cs θB pB : ℝ) : ℝ :=
  alphaB q cs θB pB / (1 - deriv (lam q) pB) *
    (1 + (lam q pB - pB * deriv (lam q) pB) /
      (pB - θB * lam q pB))

/-- Auxiliary profit curve π̇, proof of Proposition 2(i), p. 27. -/
noncomputable def piDot (q : ℝ → ℝ) (cs p : ℝ) : ℝ :=
  (p - cs - lam q p) * q p

/-- Auxiliary profit curve π̃, proof of Proposition 2(i), p. 27. -/
noncomputable def piTilde (q : ℝ → ℝ) (p : ℝ) : ℝ :=
  lam q p * q p

end AgencyPassThrough.Pricing


