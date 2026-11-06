-- Prove2me | Definitions.Def_DecodablePOMDP_Admissible
-- name    : DecodablePOMDP_Admissible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:26:08.163739+00:00
-- url     : https://prove2.me/theorems/a1d85de8-ef17-4296-b9a1-994114a53249
-- title:
--   Admissible ages $\mathcal A_h(u)$, suffix beliefs $\phi^u_{h,q}$ and $\Phi_h(u,w)$
-- statement:
--   Fix a stage $h$ and a suffix $u$.
--
--   1. A numerical age $q\in\{0,\dots,L-1\}$ is **admissible** if $\tau=h-q\ge2$, the recorded reveal observation $z_\tau=(y_\tau,\hat x_\tau)$ has $R_\tau(z_\tau\mid\hat x_\tau)>0$, and filtering from $\delta_{\hat x_\tau}$ through the recorded transitions $T_\tau,\dots,T_{h-1}$ and residual likelihoods $N_{\tau+1},\dots,N_h$ has positive total mass.
--   2. The age $\perp$ is **admissible** if $h\le L$ and filtering from $\mu_1$ through the whole recorded history with residual likelihoods has positive mass (also at $h=1$).
--   3. $\mathcal A_h(u)$ is the set of admissible ages. For an admissible age, $\phi^u_{h,q}$ is the normalised result of its filtering calculation; otherwise $\phi^u_{h,q}=\mu_1$.
--   4. For a weight vector $w$ on $\mathcal Q$, $\Phi_h(u,w)(s,q)=w_q\,\phi^u_{h,q}(s)$, and $\Phi_h(u,w)(\partial)=0$.
--
--   $\Phi_h(u,w)$ is the belief represented by the pair $(u,w)$; the planner only puts weight on admissible ages.
-- source:
--   Dobson, Jog, Shiu, Quasipolynomial-Time Planning for Decodable POMDPs (preprint, sha256 c1256cbe…3584b), §4.1, p.10; App. A.4, p.16

import Mathlib
import Definitions.Def_DecodablePOMDP_RevealResidual
import Definitions.Def_DecodablePOMDP_Suffix

namespace DecodablePOMDP

open Classical

/-- **Residual filtering through recorded steps** (p.10; A.4, p.16). `suffixFilter P D ρ h init steps`
is the unnormalised law of the hidden state at stage `h` obtained from `init` at stage
`h − steps.length` by applying, for each recorded pair `(a_k, z_{k+1})` (oldest first), the
transition `T_k(· | ·, a_k)` and the residual likelihood `N_{k+1}(z_{k+1} | ·)`. The list is newest
first: its head is `(a_{h−1}, z_h)`.

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), App. A.4, p.16: "Starting from δ_{X̂τ}, apply
transitions Tτ, . . . , Th−1 with the recorded actions and residual observation updates
Nτ+1, . . . , Nh." -/
noncomputable def suffixFilter {S A O : Type} [DecidableEq S] [Fintype S] [Fintype O]
    (P : POMDP S A O) (D : ℕ → O → S → ℝ) (ρ : ℝ) : ℕ → (S → ℝ) → List (A × (O × S)) → S → ℝ
  | _, init, [] => init
  | h, init, (a, z) :: rest => fun s' =>
      ∑ s, suffixFilter P D ρ (h - 1) init rest s * P.T (h - 1) s a s' * residual P D ρ h s' z

/-- **Recorded reveal observation** of age `q` in the suffix `u` (p.10): the observation
`z_τ`, `τ = h − q`, if it lies in `u`. The `q`-th pair (newest first) carries `z_{h−q}`; if `q`
equals the number of pairs, the observation is `first`. -/
def revealObs {A O S : Type} (u : Suffix A O S) (q : ℕ) : Option (O × S) :=
  match u.2[q]? with
  | some p => some p.2
  | none => if q = u.2.length then u.1 else none

/-- Normalisation of a nonnegative vector to a probability vector. -/
noncomputable def normalize {S : Type} [Fintype S] (f : S → ℝ) : S → ℝ :=
  fun s => f s / ∑ x, f x

/-- **Admissible age** (p.10). At stage `h` with suffix `u`:
* a numerical age `q ∈ {0, …, L−1}` is admissible if `τ = h − q ≥ 2`, the recorded reveal
  observation `z_τ = (y_τ, x̂_τ)` has `R_τ(z_τ | x̂_τ) > 0`, and filtering from `δ_{x̂_τ}` through
  the recorded transitions and residual observations at times `τ + 1, …, h` has positive likelihood;
* the age `⊥` is admissible if `h ≤ L` and filtering from `µ₁` through the full recorded history
  with residual channels has positive likelihood.

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), §4.1, p.10: "A numerical age q ∈ {0, . . . ,
L − 1} is admissible if τ = h − q ≥ 2, the recorded reveal observation has Rτ(zτ | x̂τ) > 0, and
filtering from δ_{x̂τ} through the recorded transitions and residual observations at times
τ + 1, . . . , h has positive likelihood. The age ⊥ is admissible if h ≤ L and filtering from µ1
through the full recorded history using residual channels has positive likelihood (including the
empty history at h = 1)." -/
def IsAdmissible {S A O : Type} [DecidableEq S] [Fintype S] [Fintype O] (P : POMDP S A O)
    (D : ℕ → O → S → ℝ) (ρ : ℝ) (L h : ℕ) (u : Suffix A O S) : Option (Fin L) → Prop
  | some q => ∃ z, revealObs u q.val = some z ∧ q.val + 2 ≤ h ∧
      0 < reveal P D (h - q.val) z.2 z ∧
      0 < ∑ s, suffixFilter P D ρ h (fun x => if x = z.2 then 1 else 0) (u.2.take q.val) s
  | none => h ≤ L ∧ 0 < ∑ s, suffixFilter P D ρ h P.μ₁ u.2 s

/-- **The set of admissible ages** `A_h(u)` (p.10). -/
noncomputable def admissibleSet {S A O : Type} [DecidableEq S] [Fintype S] [Fintype O]
    (P : POMDP S A O) (D : ℕ → O → S → ℝ) (ρ : ℝ) (L h : ℕ) (u : Suffix A O S) :
    Finset (Option (Fin L)) :=
  Finset.univ.filter (fun q => IsAdmissible P D ρ L h u q)

/-- **Suffix belief** `ϕ^u_{h,q}` (p.10): for an admissible age, the normalised result of the
filtering calculation of `IsAdmissible` (from `δ_{x̂_τ}` through the newest `q` pairs for a
numerical age, from `µ₁` through all of `u` for `⊥`); for an inadmissible age, `µ₁`.

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), §4.1, p.10: "For admissible ages, define
ϕ^u_{h,q} by this calculation; otherwise set it to µ1." -/
noncomputable def phiU {S A O : Type} [DecidableEq S] [Fintype S] [Fintype O]
    (P : POMDP S A O) (D : ℕ → O → S → ℝ) (ρ : ℝ) (L h : ℕ) (u : Suffix A O S)
    (q : Option (Fin L)) : S → ℝ :=
  if IsAdmissible P D ρ L h u q then
    match q with
    | some r => match revealObs u r.val with
      | some z => normalize (suffixFilter P D ρ h (fun x => if x = z.2 then 1 else 0)
          (u.2.take r.val))
      | none => P.μ₁
    | none => normalize (suffixFilter P D ρ h P.μ₁ u.2)
  else P.μ₁

/-- **Belief of a (suffix, weight) pair** `Φ_h(u, w)(s, q) := w_q ϕ^u_{h,q}(s)` (Lemma 5, p.10),
a vector on the killed states `(S × Q) ∪ {∂}`, zero at `∂`.

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), Lemma 5, p.10: "β(s, q) = Φh(u, w)(s, q) =
wqϕ^u_{h,q}(s)". -/
noncomputable def Phi {S A O : Type} [DecidableEq S] [Fintype S] [Fintype O]
    (P : POMDP S A O) (D : ℕ → O → S → ℝ) (ρ : ℝ) (L h : ℕ) (u : Suffix A O S)
    (w : Option (Fin L) → ℝ) : Option (S × Option (Fin L)) → ℝ
  | none => 0
  | some (s, q) => w q * phiU P D ρ L h u q s

end DecodablePOMDP


