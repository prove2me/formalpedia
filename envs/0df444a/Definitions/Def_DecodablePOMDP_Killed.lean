-- Prove2me | Definitions.Def_DecodablePOMDP_Killed
-- name    : DecodablePOMDP_Killed
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:25:54.59608+00:00
-- url     : https://prove2.me/theorems/9081f33a-c5f0-4e5f-baaa-bd3e0e4ea150
-- title:
--   The $L$-killed POMDP $\widetilde{\mathcal P}(L)$ and the extension of its policies
-- statement:
--   Fix $L\ge1$, $\rho\in(0,1]$, $c=\rho/2$ and a $\rho$-decoder family. Let $\mathcal Q=\{\perp,0,1,\dots,L-1\}$ (the age of the last reveal). The **$L$-killed POMDP** $\widetilde{\mathcal P}(L)$ has states $(\mathcal S\times\mathcal Q)\cup\{\partial\}$, observations $(\mathcal O\times\mathcal S)\cup\{\dagger\}$, the horizon and actions of $\mathcal P$, and:
--
--   1. initial state $(X_1,\perp)$ with $X_1\sim\mu_1$;
--   2. from an alive $(x,q)$ at time $h$ with action $a$: draw $x'\sim T_h(\cdot\mid x,a)$ and, independently, $F_{h+1}\sim\mathrm{Bern}(c)$; if $F_{h+1}=1$ the next state is $(x',0)$; if $F_{h+1}=0$ it is $(x',q+1)$ for $q\le L-2$, $\partial$ for $q=L-1$, $(x',\perp)$ for $q=\perp$ and $h<L$, and $\partial$ for $q=\perp$ and $h\ge L$; the state $\partial$ is absorbing;
--   3. observation $R_h(\cdot\mid x)$ in $(x,0)$, $N_h(\cdot\mid x)$ in $(x,q)$ with $q\ne0$, and $\dagger$ in $\partial$;
--   4. reward $r_h(y)$ for $z=(y,\hat s)$ and $0$ for $\dagger$.
--
--   It evolves like $\widehat{\mathcal P}$ until a run of $L$ consecutive residual observations occurs and then earns nothing.
--
--   A policy $\pi_L$ of $\widetilde{\mathcal P}(L)$ **extends** to the policy of $\widehat{\mathcal P}$ that plays, after an augmented history, what $\pi_L$ plays after the same history read as an alive history (App. A.3).
--
--   **Formalization Note** $\perp$ is `none` and the age $r$ is `some r`; $\partial$ and $\dagger$ are `none`. The augmented POMDP never emits $\dagger$, so the extension needs no arbitrary choice.
-- source:
--   Dobson, Jog, Shiu, Quasipolynomial-Time Planning for Decodable POMDPs (preprint, sha256 c1256cbe…3584b), §3, pp.7–8; App. A.3, p.15

import Mathlib
import Definitions.Def_DecodablePOMDP_RevealResidual
import Definitions.Def_DecodablePOMDP_Value

namespace DecodablePOMDP

/-- **Age after a residual step** (pp.7–8). For the reveal age `q ∈ Q = {⊥, 0, …, L−1}`
(`none = ⊥`, `some r = r`) at transition time `h`, the outcome of `F_{h+1} = 0`:
`some q'` is the surviving age, `none` means the process is killed (moves to `∂`).
`r ↦ r + 1` if `r ≤ L − 2`, killed if `r = L − 1`; `⊥ ↦ ⊥` if `h < L`, killed if `h ≥ L`.

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), §3, p.8: "When Qh = r ∈ {0, . . . , L − 2},
the new state is (Xh+1, Qh + 1). When Qh = L − 1, sampling Fh+1 = 0 leads to run of L zeros, which
updates the state to the cemetery state ∂. When Qh = ⊥ … sampling Fh+1 = 0 keeps Qh+1 = ⊥ when
h < L, and kills the process by moving to ∂ when h ≥ L." -/
def ageNext (L h : ℕ) : Option (Fin L) → Option (Option (Fin L))
  | some r => if hr : r.val + 1 < L then some (some ⟨r.val + 1, hr⟩) else none
  | none => if h < L then some none else none

/-- Indicator that the age is `0` (a reveal has just occurred). -/
def isAgeZero {L : ℕ} : Option (Fin L) → Bool
  | some r => r.val == 0
  | none => false

/-- **L-killed POMDP** `P̃(L)` (§3, pp.7–8), with reveal/residual channels of the ρ-decoders `D`
and mixing coefficient `c = ρ/2`.

* states `S̃ = (S × Q) ∪ {∂}` = `Option (S × Option (Fin L))` (`none = ∂`, `some (x, none) = (x, ⊥)`);
* observations `Õ = (O × S) ∪ {†}` = `Option (O × S)` (`none = †`);
* `μ̃₁` is `μ₁` on `S × {⊥}`;
* from an alive `(x, q)` at time `h` with action `a`: propose `x' ∼ T_h(· | x, a)`, and
  independently `F_{h+1} ∼ Bern(c)`; `F = 1` gives `(x', 0)`; `F = 0` gives `(x', q')` with
  `q' = ageNext L h q`, or `∂` if that is `none`; `∂` stays at `∂`;
* observation at `h ≥ 2`: `R_h(· | x)` in `(x, 0)`, `N_h(· | x)` in `(x, q)` with `q ≠ 0`, `†` in `∂`;
* reward `r_h(y)` for `z = (y, ŝ)`, `0` for `†`.

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), §3, pp.7–8: "Let Q := {⊥, 0, 1, . . . , L − 1}
… define S̃ := (S × Q) ∪ {∂} … Õ := Z ∪ {†} = (O × S) ∪ {†}. … The initial hidden state is (X1, ⊥),
where X1 ∼ µ1. … Suppose the process is alive at time h < H, with hidden state (Xh, Qh), and action
ah is taken. Generate a proposed Xh+1 according to Th(· | Xh, ah) and, independently, sample
Fh+1 ∼ Bern(c). If Fh+1 = 1, the next state is (Xh+1, 0). If Fh+1 = 0, the next hidden state is
determined as follows. When Qh = r ∈ {0, . . . , L − 2}, the new state is (Xh+1, Qh + 1). When
Qh = L − 1, sampling Fh+1 = 0 leads to run of L zeros, which updates the state to the cemetery state
∂. When Qh = ⊥ … sampling Fh+1 = 0 keeps Qh+1 = ⊥ when h < L, and kills the process by moving to ∂
when h ≥ L. Once the process enters ∂, it remains there regardless of future actions. For time
h ≥ 2, the observation channel depends on Qh. If the hidden state is (Xh, 0), generate Zh from the
reveal channel Rh(· | Xh). If the hidden state is (Xh, Qh) with Qh ∈ {⊥, 1, . . . , L − 1},
generate Zh from the residual channel Nh(· | Xh). If the hidden state is ∂, emit † with probability
one. The reward for an observation Zh = (Yh, X̂h) is the same reward as in P̂ … The cemetery
observation † receives reward zero."

**Formalization Note.** `L ≥ 1` and `ρ ∈ (0, 1]` are hypotheses of every statement using this
POMDP; the kernels are written for all `h` and only `h ∈ [1 : H−1]` (transitions) and
`h ∈ [2 : H]` (observations, rewards) are read. -/
noncomputable def killed {S A O : Type} [DecidableEq S] [Fintype O] (P : POMDP S A O)
    (D : ℕ → O → S → ℝ) (ρ : ℝ) (L : ℕ) :
    POMDP (Option (S × Option (Fin L))) A (Option (O × S)) where
  H := P.H
  μ₁ ξ := match ξ with
    | some (x, none) => P.μ₁ x
    | _ => 0
  T h ξ a ξ' := match ξ, ξ' with
    | none, none => 1
    | none, some _ => 0
    | some (_, q), none => if ageNext L h q = none then 1 - ρ / 2 else 0
    | some (x, q), some (x', q') =>
        P.T h x a x' * ((if isAgeZero q' then ρ / 2 else 0) +
          (if ageNext L h q = some q' then 1 - ρ / 2 else 0))
  K h ξ z := match ξ, z with
    | none, none => 1
    | none, some _ => 0
    | some _, none => 0
    | some (x, q), some z => if isAgeZero q then reveal P D h x z else residual P D ρ h x z
  r h z := match z with
    | none => 0
    | some z => P.r h z.1

/-- **Extension of a killed-POMDP policy to the augmented POMDP** (Lemma 3, p.8; A.3, p.15): the
augmented policy plays, after the augmented history `(a_i, z_i)`, what `π_L` plays after the alive
history `(a_i, some z_i)`.

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), App. A.3, p.15: "define a policy π for the
augmented POMDP that agrees with πL on every alive history hh before the process is killed; and
behaves arbitrarily on histories that have already produced a cemetery observation †".

**Formalization Note.** The augmented POMDP never emits `†`, so every augmented history corresponds
to an alive killed history and no arbitrary choice is needed. -/
def extendPolicy {A O S : Type} (π : PolicyFn A (Option (O × S))) : PolicyFn A (O × S) :=
  fun t hist => π t (fun i => ((hist i).1, some (hist i).2))

end DecodablePOMDP


