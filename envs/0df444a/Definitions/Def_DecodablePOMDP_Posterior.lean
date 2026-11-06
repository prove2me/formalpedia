-- Prove2me | Definitions.Def_DecodablePOMDP_Posterior
-- name    : DecodablePOMDP_Posterior
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:26:52.585354+00:00
-- url     : https://prove2.me/theorems/b151088e-5eac-416b-8fbc-0bc025d9f6f1
-- title:
--   Posterior reveal-age weights $w_{h,q}$ and conditional state beliefs $\phi_{h,q}$
-- statement:
--   Let $\pi$ be a policy of $\widetilde{\mathcal P}(L)$ and $h_h$ an alive history at time $h$. Its probability is $\Pr(H_h=h_h)$, and, when it is positive,
--
--   $$w_{h,q}(h_h)=\Pr(Q_h=q\mid H_h=h_h),\qquad \phi_{h,q}(s;h_h)=\Pr(X_h=s\mid Q_h=q,H_h=h_h)\quad(w_{h,q}>0).\tag{5}$$
--
--   The joint belief is $\beta_h(s,q)=w_{h,q}\,\phi_{h,q}(s)$: a mixture of at most $L+1$ state beliefs indexed by the age of the last reveal.
--
--   **Formalization Note** All three are ratios of finite sums of the joint law of state and history. An alive history is one whose observations are all in $\mathcal O\times\mathcal S$.
-- source:
--   Dobson, Jog, Shiu, Quasipolynomial-Time Planning for Decodable POMDPs (preprint, sha256 c1256cbe…3584b), §4.1, p.9, (5)

import Mathlib
import Definitions.Def_DecodablePOMDP_Killed

namespace DecodablePOMDP

/-- An alive history of the killed POMDP: the observations `z_i ∈ O × S` read as `some z_i`. -/
def liftHist {A O S : Type} {t : ℕ} (hist : Hist A (O × S) t) : Hist A (Option (O × S)) t :=
  fun i => ((hist i).1, some (hist i).2)

/-- **Probability of an alive history** `Pr(H_h = h_h)` in `P̃(L)` under the policy `π`, for the
history of `t` steps (`h = t + 1`).

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), §4.1, p.9: "Let hh be an alive history
realisation (alive meaning its latest observation is not a †) with Pr(Hh = hh) > 0." -/
noncomputable def histProb {S A O : Type} [DecidableEq S] [Fintype S] [Fintype O] (P : POMDP S A O)
    (D : ℕ → O → S → ℝ) (ρ : ℝ) (L : ℕ) (π : PolicyFn A (Option (O × S))) (t : ℕ)
    (hist : Hist A (O × S) t) : ℝ :=
  ∑ ξ, jointFrom (killed P D ρ L) 1 (killed P D ρ L).μ₁ π t (liftHist hist) ξ

/-- **Posterior reveal-age weight** `w_{h,q}(h_h) := Pr(Q_h = q | H_h = h_h)` (§4.1, p.9), in
`P̃(L)` under `π`, for the history of `t` steps (`h = t + 1`).

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), §4.1, p.9: "the probability distribution of
the most recent revelation time given the history, given by wh,q = wh,q(hh) := Pr(Qh = q|Hh = hh)".

**Formalization Note.** A ratio of finite sums; it is only used when `Pr(H_h = h_h) > 0`. -/
noncomputable def posteriorWeight {S A O : Type} [DecidableEq S] [Fintype S] [Fintype O]
    (P : POMDP S A O) (D : ℕ → O → S → ℝ) (ρ : ℝ) (L : ℕ) (π : PolicyFn A (Option (O × S)))
    (t : ℕ) (hist : Hist A (O × S) t) (q : Option (Fin L)) : ℝ :=
  (∑ x, jointFrom (killed P D ρ L) 1 (killed P D ρ L).μ₁ π t (liftHist hist) (some (x, q))) /
    histProb P D ρ L π t hist

/-- **Conditional state belief** `ϕ_{h,q}(s; h_h) := Pr(X_h = s | Q_h = q, H_h = h_h)` (§4.1, p.9,
(5)), in `P̃(L)` under `π`, for the history of `t` steps (`h = t + 1`).

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), §4.1, p.9: "If wh,q > 0, define the belief of
the current state conditioned on Qh = q and Hh = hh as ϕh,q(s) = ϕh,q(s; hh) := Pr(Xh = s|Qh = q,
Hh = hh). (5)"

**Formalization Note.** A ratio of finite sums; it is only used when `w_{h,q} > 0`. -/
noncomputable def posteriorState {S A O : Type} [DecidableEq S] [Fintype S] [Fintype O]
    (P : POMDP S A O) (D : ℕ → O → S → ℝ) (ρ : ℝ) (L : ℕ) (π : PolicyFn A (Option (O × S)))
    (t : ℕ) (hist : Hist A (O × S) t) (q : Option (Fin L)) (s : S) : ℝ :=
  jointFrom (killed P D ρ L) 1 (killed P D ρ L).μ₁ π t (liftHist hist) (some (s, q)) /
    ∑ x, jointFrom (killed P D ρ L) 1 (killed P D ρ L).μ₁ π t (liftHist hist) (some (x, q))

end DecodablePOMDP


