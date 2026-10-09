-- Prove2me | Definitions.Def_BalancedPrices_ClosureMax_Composition
-- name    : BalancedPrices_ClosureMax_Composition
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T16:55:30.216464+00:00
-- url     : https://prove2.me/theorems/100b638c-8975-4612-ad84-f21629c9ee5c
-- title:
--   §5 and Appendix B — finite maxima, supporting valuations, consistency, and product markets
-- statement:
--   **Closure under maximum (§5, p. 554).** Given a valuation space $V_i$ for agent $i$, its extension $V_i^{\max}$ contains every function $v_i:X_i\to\mathbb R$ for which there is a finite nonempty set $\{v_i^1,\dots,v_i^m\}\subseteq V_i$ with
--   $$v_i(x_i)=\max_{\ell} v_i^\ell(x_i)\quad\text{for all }x_i\in X_i.$$
--   A profile $\tilde v\in V$ is a **supporting valuation profile** for an allocation $x$ and a profile $v\in V^{\max}$ if $\tilde v_i\le v_i$ pointwise and $\tilde v_i(x_i)=v_i(x_i)$ for every agent $i$.
--
--   **Definition 5.1.** An allocation rule ALG is **consistent** if for every $v\in V^{\max}$ and every supporting profile $\tilde v\in V$ for $\operatorname{ALG}(v)$, $\tilde v(\operatorname{ALG}(\tilde v))\ge\tilde v(\operatorname{ALG}(v))$.
--
--   **Definition B.1.** ALG is **strongly consistent** if moreover $v(\operatorname{ALG}(v))\ge v(\operatorname{ALG}(\tilde v))$ for all such $v,\tilde v$.
--
--   **Definition 3.4.** A pricing rule is **weakly $(\alpha,\beta_1,\beta_2)$-balanced** if it satisfies condition (a) of Definition 3.1 and, for every $x\in\mathcal F$ and $x'\in\mathcal F_x$,
--   $$\sum_i p_i(x'_i\mid x_{[i-1]})\le\beta_1\,v(\operatorname{OPT}(v,\mathcal F_x))+\beta_2\,v(\operatorname{ALG}(v)).$$
--
--   **Closure under addition (pp. 554–555).** For $m$ allocation problems on the same agents, with outcome spaces $X_i^\ell$ and feasible sets $\mathcal F^\ell$, the joint outcome of agent $i$ is $x_i=(x_i^1,\dots,x_i^m)$ and the joint feasible set is $\mathcal F=\mathcal F^1\times\dots\times\mathcal F^m$. An additive valuation is $v_i(x_i)=\sum_\ell v_i^\ell(x_i^\ell)$, the summed pricing rule is $p_i(x_i\mid y)=\sum_\ell p_i^\ell(x_i^\ell\mid y^\ell)$, and the joint allocation rule is $\operatorname{ALG}(v)=(\operatorname{ALG}^1(v^1),\dots,\operatorname{ALG}^m(v^m))$.
--
--   These objects are used by Theorems 5.3, 5.4, B.2 and B.3 and by Lemma 5.2.
--
--   **Formalization Note** The maximum is `Finset.sup'` over a nonempty `Finset` of functions in $V_i$; nonemptiness is implicit in "$\max_\ell$". Consistency and strong consistency quantify only over $V^{\max}$ profiles and supporting profiles in $V$, as printed. In the product construction the joint outcome of agent $i$ is the dependent function `∀ ℓ, Y ℓ i`, and markets are indexed by `Fin m` from zero.
-- source:
--   Dütting, Feldman, Kesselheim, Lucier, Prophet inequalities made easy: Stochastic optimization by pricing nonstochastic inputs, SIAM J. Comput. 49 (2020), pp. 551, 554–555, 561–562, Definitions 3.4, 5.1, B.1 and Theorems 5.4, B.3

import Mathlib
import Definitions.Def_BalancedPrices_Extension_Model
import Definitions.Def_BalancedPrices_WeakExtension_Model

namespace BalancedPrices.ClosureMax

/-- A nonempty finite pointwise maximum of valuations from the base space. -/
def VmaxSet {n : ℕ} {X : Fin n → Type*}
    (Vsp : ∀ i, Set (X i → ℝ)) (i : Fin n) : Set (X i → ℝ) :=
  {g | ∃ (s : Finset (X i → ℝ)) (hs : s.Nonempty),
    (s : Set (X i → ℝ)) ⊆ Vsp i ∧
    ∀ xi, g xi = s.sup' hs (fun f => f xi)}

/-- A base valuation supporting an extended one at allocation `x`. -/
def IsSupporting {n : ℕ} {X : Fin n → Type*}
    (Vsp : ∀ i, Set (X i → ℝ)) (vt : BalancedPrices.Extension.Valuation X)
    (x : BalancedPrices.Extension.Outcome X) (vf : BalancedPrices.Extension.Valuation X) : Prop :=
  ∀ i, vt i ∈ Vsp i ∧ (∀ xi, vt i xi ≤ vf i xi) ∧
    vt i (x i) = vf i (x i)

/-- Definition 5.1. -/
def Consistent {n : ℕ} {X : Fin n → Type*}
    (Vsp : ∀ i, Set (X i → ℝ))
    (ALG : BalancedPrices.Extension.Valuation X → BalancedPrices.Extension.Outcome X) : Prop :=
  ∀ vf, (∀ i, vf i ∈ VmaxSet Vsp i) →
    ∀ vt, IsSupporting Vsp vt (ALG vf) vf →
      BalancedPrices.Extension.welfare vt (ALG vf) ≤ BalancedPrices.Extension.welfare vt (ALG vt)

/-- Definition B.1. -/
def StronglyConsistent {n : ℕ} {X : Fin n → Type*}
    (Vsp : ∀ i, Set (X i → ℝ))
    (ALG : BalancedPrices.Extension.Valuation X → BalancedPrices.Extension.Outcome X) : Prop :=
  Consistent Vsp ALG ∧
    ∀ vf, (∀ i, vf i ∈ VmaxSet Vsp i) →
      ∀ vt, IsSupporting Vsp vt (ALG vf) vf →
        BalancedPrices.Extension.welfare vf (ALG vt) ≤ BalancedPrices.Extension.welfare vf (ALG vf)

/-- The null outcome of a product market. -/
def jointNull {m n : ℕ} {Y : Fin m → Fin n → Type*}
    (nulY : ∀ ℓ i, Y ℓ i) : BalancedPrices.Extension.Outcome (fun i => ∀ ℓ, Y ℓ i) :=
  fun i ℓ => nulY ℓ i

/-- The allocation in market `ℓ` extracted from a joint allocation. -/
def component {m n : ℕ} {Y : Fin m → Fin n → Type*}
    (x : BalancedPrices.Extension.Outcome (fun i => ∀ ℓ, Y ℓ i)) (ℓ : Fin m) : BalancedPrices.Extension.Outcome (Y ℓ) :=
  fun i => x i ℓ

def jointFeasible {m n : ℕ} {Y : Fin m → Fin n → Type*}
    (Fl : ∀ ℓ, Set (BalancedPrices.Extension.Outcome (Y ℓ))) :
    Set (BalancedPrices.Extension.Outcome (fun i => ∀ ℓ, Y ℓ i)) :=
  {x | ∀ ℓ, component x ℓ ∈ Fl ℓ}

def jointVal {m n : ℕ} {Y : Fin m → Fin n → Type*}
    (vl : ∀ ℓ, BalancedPrices.Extension.Valuation (Y ℓ)) :
    BalancedPrices.Extension.Valuation (fun i => ∀ ℓ, Y ℓ i) :=
  fun i xi => ∑ ℓ, vl ℓ i (xi ℓ)

noncomputable def jointPrice {m n : ℕ} {Y : Fin m → Fin n → Type*}
    (pl : ∀ ℓ, BalancedPrices.Extension.PriceRule (Y ℓ)) :
    BalancedPrices.Extension.PriceRule (fun i => ∀ ℓ, Y ℓ i) :=
  fun i xi y => ∑ ℓ, pl ℓ i (xi ℓ) (component y ℓ)

def jointALG {m n : ℕ} {Y : Fin m → Fin n → Type*}
    (ALGl : ∀ ℓ, BalancedPrices.Extension.Valuation (Y ℓ) → BalancedPrices.Extension.Outcome (Y ℓ))
    (vl : ∀ ℓ, BalancedPrices.Extension.Valuation (Y ℓ)) :
    BalancedPrices.Extension.Outcome (fun i => ∀ ℓ, Y ℓ i) :=
  fun i ℓ => ALGl ℓ (vl ℓ) i

end BalancedPrices.ClosureMax


