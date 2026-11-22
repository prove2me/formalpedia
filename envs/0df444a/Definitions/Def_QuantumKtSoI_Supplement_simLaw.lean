-- Prove2me | Definitions.Def_QuantumKtSoI_Supplement_simLaw
-- name    : QuantumKtSoI_Supplement_simLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:32:35.51886+00:00
-- url     : https://prove2.me/theorems/cce69607-f093-402d-abb3-536b6cceae6f
-- title:
--   The scheduled evaluation $\mathrm{sim}^D_f(z)$ (Definition D.7), budgets $L_k$, first-halt law, amplification depth, $K_D$
-- statement:
--   For a description $f$ and a string $z$, the **first-halt law** $f^{hz}_f(h,w)$ is the weight of the record sequences of $M(f)$ on $z$ that first reach a final state after exactly $h$ steps with output $w$, so that $P_f(z;s,w)=\sum_{h\le s}f^{hz}_f(h,w)$. The **amplification depth** $\mathrm{ad}(f)$ is the largest number of $\mathrm{AMP}$ constructors on a root-to-leaf path of the parse of $f$, and $\mathrm{fin}_0(f)$ says syntactically that $M(f)$ starts in a final state. For an integer $D\ge1$ the **budgets** are $L_0=0$, $L_k=L_{k-1}+\max(1,\lceil L_{k-1}/D\rceil)$, and
--   $$K_D(a)=\sum_{j=0}^{a}(1+1/D)^j .$$
--   The **scheduled evaluation** $\mathrm{sim}^D_f(z)$ is a random pair $(\lambda,o)$, $\lambda\in\mathbb N\cup\{\infty\}$ its units and $o$ a string or $\bot$, defined by induction on the parse:
--
--   1. for $\mathrm{BASE}(A)$ or $\mathrm{LIT}(d)$, $\Pr[\lambda=s,o=w]=f^{hz}_f(s,w)$ and $(\lambda,o)=(\infty,\bot)$ on the remaining probability;
--   2. for $\mathrm{SEQ}_g(f_1,f_2)$, draw $(\lambda_1,u)$ from $\mathrm{sim}^D_{f_1}(z)$ and, if finite, $(\lambda_2,v)$ independently from $\mathrm{sim}^D_{f_2}(\alpha_g(z,u))$; if both are finite, $o=\beta_g(z,u,v)$ and $\lambda=\lambda_1+|\alpha_g(z,u)|+\lambda_2+\max(|\beta_g(z,u,v)|,1)$, otherwise $(\infty,\bot)$;
--   3. for $\mathrm{AMP}(r,f')$ with $\mathrm{fin}_0(f')$, $(\lambda,o)=(0,\epsilon)$;
--   4. for $\mathrm{AMP}(r,f')$ otherwise, draw $r$ independent pairs $(\ell_i,w_i)$ from $\mathrm{sim}^D_{f'}(z)$; with $\mathrm{cnt}_k(v)=\#\{i:\ell_i\le L_k,\ w_i=v\}$ and $k_\star$ the least $k\ge1$ such that some $v$ has $\mathrm{cnt}_k(v)>r/2$ or every $\ell_i\le L_k$, the output is that $v$ if there is one and $\epsilon$ otherwise, and $\lambda=\sum_i\min(\ell_i,L_{k_\star})$; if there is no such $k$, $(\infty,\bot)$.
--
--   Theorem D.9 compares this law with the output law of $M(f)$.
--
--   **Formalization Note** The law is a mass function on outcomes $(\lambda,o)\in\mathbb N_\infty\times\mathrm{Option}(\{0,1\}^*)$ with values in $[0,\infty]$. The first-halt law is defined from the displayed identity as $P_f(z;h,w)-P_f(z;h-1,w)$.
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), Appendix D, pp.149–153 (first-halt law and ad, p.149; fin₀ and budgets, p.152; Definition D.7, p.152; K_D, p.153)

import Mathlib
import Definitions.Def_QuantumKtSoI_Desc

open Classical

noncomputable section

namespace QuantumKtSoI.Supplement

/-- The first-halt law `f^{hz}_f(h, w)` (Appendix D, p.149 of Myrisiotis, STOC 2027 submission,
held version sha256 6616571c…): the sum of `‖ψ_ρ‖²` over the complete record sequences of `M(f)` on
`z` of length `h` with output `w`.

**Formalization Note** The paper notes `P_f(z; s, w) = Σ_{h ≤ s} f^{hz}_f(h, w)` for every `s ≥ 0`
(p.149); the definition inverts this identity: `f^{hz}_f(0, w) = P_f(z; 0, w)` and
`f^{hz}_f(h, w) = P_f(z; h, w) − P_f(z; h − 1, w)` for `h ≥ 1`. -/
def fhz (G : GlueRoutines) (f : Desc) (z : List Bool) (h : ℕ) (w : List Bool) : ℝ :=
  if h = 0 then f.prob G z 0 w else f.prob G z h w - f.prob G z (h - 1) w

/-- The **amplification depth** `ad(f)` (p.149): the largest number of `AMP` constructors on a path
from the root to a leaf of the parse of `f`. -/
def ad : Desc → ℕ
  | .base _ => 0
  | .lit _ => 0
  | .seq _ e₁ e₂ => max (ad e₁) (ad e₂)
  | .amp _ e => ad e + 1

/-- `fin₀(f)` (p.152): `fin₀(BASE(A))` holds iff the initial state of `A` is final;
`fin₀(LIT(d))` and `fin₀(SEQ_g(f₁, f₂))` are false; `fin₀(AMP(r, f′)) = fin₀(f′)`. -/
def fin0 : Desc → Prop
  | .base A => A.1.toMachine.isFinal A.1.toMachine.init = true
  | .lit _ => False
  | .seq _ _ _ => False
  | .amp _ e => fin0 e

/-- The budgets `L₀ = 0`, `L_k = L_{k−1} + max(1, ⌈L_{k−1}/D⌉)` for an integer `D ≥ 1` (p.152). -/
def budget (D : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => budget D k + max 1 ⌈((budget D k : ℝ) / D)⌉₊

/-- `K_D(a) = Σ_{j=0}^{a} (1 + 1/D)^j` (p.153). -/
def KD (D a : ℕ) : ℝ := ∑ j ∈ Finset.range (a + 1), (1 + 1 / (D : ℝ)) ^ j

/-- The outcomes `(λ, o)` of a scheduled evaluation: units `λ ∈ ℕ ∪ {∞}` and an output `o`, a
string or `⊥` (`none`). -/
abbrev Outcome : Type := ℕ∞ × Option (List Bool)

/-- The outcome of the repetition clause of Definition D.7 (p.152) for `r` drawn pairs
`ω i = (ℓ_i, w_i)`: with `cnt_k(v) = #{i : ℓ_i ≤ L_k, w_i = v}` and `k⋆` the least `k ≥ 1` such
that some `v` has `cnt_k(v) > r/2` or every `ℓ_i ≤ L_k`, the output is the `v` with
`cnt_{k⋆}(v) > r/2` if there is one and `ε` otherwise, and `λ = Σ_i min(ℓ_i, L_{k⋆})`; if there is no
such `k`, the outcome is `(∞, ⊥)`. -/
def ampOutcome (D r : ℕ) (ω : Fin r → Outcome) : Outcome :=
  let cnt : ℕ → List Bool → ℕ := fun k v =>
    (Finset.univ.filter fun i => (ω i).1 ≤ (budget D k : ℕ∞) ∧ (ω i).2 = some v).card
  let P : ℕ → Prop := fun k => 1 ≤ k ∧ ((∃ v, r < 2 * cnt k v) ∨ ∀ i, (ω i).1 ≤ (budget D k : ℕ∞))
  if h : ∃ k, P k then
    let ks := Nat.find h
    (∑ i, min (ω i).1 (budget D ks : ℕ∞),
      if hv : ∃ v, r < 2 * cnt ks v then some (Classical.choose hv) else some [])
  else (⊤, none)

/-- **Definition D.7** (Scheduled evaluation, p.152): the law of the random pair
`sim^D_f(z) = (λ, o)` (for the glue routines `G` fixing `P_f`), as a mass function on outcomes, defined by induction on the parse of `f`.
* `BASE(A)`, `LIT(d)`: `Pr[λ = s, o = w] = f^{hz}_f(s, w)`, and `(λ, o) = (∞, ⊥)` on the remaining
  probability.
* `SEQ_g(f₁, f₂)`: draw `(λ₁, u)` from `sim^D_{f₁}(z)`; if `λ₁ < ∞` draw `(λ₂, v)` independently from
  `sim^D_{f₂}(α_g(z, u))`; if both are finite, `o = β_g(z, u, v)` and
  `λ = λ₁ + |α_g(z, u)| + λ₂ + max(|β_g(z, u, v)|, 1)`; otherwise `(∞, ⊥)`.
* `AMP(r, f′)` with `fin₀(f′)`: `(λ, o) = (0, ε)`.
* `AMP(r, f′)` otherwise: draw `r` independent pairs from `sim^D_{f′}(z)` and apply `ampOutcome`.

**Formalization Note** The law is a function `Outcome → ℝ≥0∞`; probabilities of events are sums of
it. Outcomes `(s, ⊥)` with `s` finite and `(∞, w)` carry mass `0`. -/
def simLaw (G : GlueRoutines) (D : ℕ) : Desc → List Bool → Outcome → ENNReal
  | .base A, z => fun o =>
      if o.1 = ⊤ then
        (if o.2 = none then
          1 - ∑' s : ℕ, ∑' w : List Bool, ENNReal.ofReal (fhz G (.base A) z s w) else 0)
      else match o.2 with
        | some w => ENNReal.ofReal (fhz G (.base A) z o.1.toNat w)
        | none => 0
  | .lit d, z => fun o =>
      if o.1 = ⊤ then
        (if o.2 = none then
          1 - ∑' s : ℕ, ∑' w : List Bool, ENNReal.ofReal (fhz G (.lit d) z s w) else 0)
      else match o.2 with
        | some w => ENNReal.ofReal (fhz G (.lit d) z o.1.toNat w)
        | none => 0
  | .seq g e₁ e₂, z => fun o =>
      (if o = (⊤, none) then
        simLaw G D e₁ z (⊤, none) +
          ∑' s₁ : ℕ, ∑' u : List Bool,
            simLaw G D e₁ z ((s₁ : ℕ∞), some u) * simLaw G D e₂ (g.alpha z u) (⊤, none)
      else 0) +
      ∑' s₁ : ℕ, ∑' u : List Bool, ∑' s₂ : ℕ, ∑' v : List Bool,
        if o = (((s₁ + (g.alpha z u).length + s₂ + max (g.beta z u v).length 1 : ℕ) : ℕ∞),
            some (g.beta z u v)) then
          simLaw G D e₁ z ((s₁ : ℕ∞), some u) * simLaw G D e₂ (g.alpha z u) ((s₂ : ℕ∞), some v)
        else 0
  | .amp r e, z => fun o =>
      if fin0 e then (if o = (0, some []) then 1 else 0)
      else ∑' ω : Fin r → Outcome,
        (∏ i, simLaw G D e z (ω i)) * (if ampOutcome D r ω = o then 1 else 0)

end QuantumKtSoI.Supplement


