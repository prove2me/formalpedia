-- Prove2me | Definitions.Def_RamadgeWonham_Shared_Supervisor
-- name    : RamadgeWonham_Shared_Supervisor
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:36:45.114+00:00
-- url     : https://prove2.me/theorems/fea28ef7-1507-4a2a-a8e4-4c84986d4432
-- title:
--   Supervisor, closed loop 𝒮/𝒢, L_c, complete / nonblocking / nonrejecting / proper (§2.4, §3.1, §6)
-- statement:
--   Fix a generator $\mathcal G = (Q, \Sigma, \delta, q_0, Q_m)$ and a set $\Sigma_c \subseteq \Sigma$ of **controllable** events. A **supervisor** is a pair $\mathcal S = (S, \phi)$ where $S = (X, \Sigma, \xi, x_0, X_m)$ is a deterministic automaton with a (possibly infinite) state set $X$ and partial transition function $\xi$, and $\phi : X \to \{0,1\}^{\Sigma_c}$ is the **state feedback map**. Each $\phi(x)$ is extended to all of $\Sigma$ by $\phi(x)(\sigma) = 1$ for $\sigma \in \Sigma - \Sigma_c$: uncontrollable events are always enabled.
--
--   The **closed loop** $\mathcal S/\mathcal G$ is the generator on $X \times Q$ started at $(x_0, q_0)$, with marker set $X_m \times Q_m$, whose transition on $\sigma$ from $(x, q)$ is $(\xi(\sigma, x), \delta(\sigma, q))$, defined exactly when $\delta(\sigma, q)$ is defined, $\phi(x)(\sigma) = 1$, and $\xi(\sigma, x)$ is defined. Its generated and marked languages are $L(\mathcal S/\mathcal G)$ and $L_m(\mathcal S/\mathcal G)$, and the **controlled language** is
--
--   $$L_c(\mathcal S/\mathcal G) := L(\mathcal S/\mathcal G) \cap L_m(\mathcal G).$$
--
--   $\mathcal S$ is **complete** if for all $s \in \Sigma^*$ and $\sigma \in \Sigma$: whenever $s \in L(\mathcal S/\mathcal G)$, $s\sigma \in L(\mathcal G)$ and $\sigma$ is enabled at $\xi(s, x_0)$, then $s\sigma \in L(\mathcal S/\mathcal G)$. $\mathcal S$ is **nonblocking** if $\bar L_c(\mathcal S/\mathcal G) = L(\mathcal S/\mathcal G)$, **nonrejecting** if $\bar L_c(\mathcal S/\mathcal G) = \bar L_m(\mathcal S/\mathcal G)$, and **proper** if it is complete, nonblocking and nonrejecting, i.e. complete with
--   $$\bar L_m(\mathcal S/\mathcal G) = \bar L_c(\mathcal S/\mathcal G) = L(\mathcal S/\mathcal G).$$
--
--   These notions state what it means for a feedback controller to realize a prescribed closed-loop behaviour without stopping the plant arbitrarily (completeness) and without deadlocking (nonblocking).
--
--   This definition is shared by both missions of this series: 1 (synthesis: Propositions 4.1, p. 212, and 5.1, p. 214; Theorem 6.1, p. 216; the Supervisory Marking and Control Problems of §7, p. 217, and Theorem 7.1, pp. 218–219) and 2 (quotient structure: projections of supervisors and Proposition 8.1, p. 219; Theorem 10.1 and the steps of its proof, pp. 222–224).
--
--   **Formalization Note.** $\phi$ is `φ : S.Q → Ec → Bool`, and "$\sigma$ enabled at $x$" is `∀ h : σ ∈ Ec, φ x ⟨σ, h⟩ = true`, which is automatically true off $\Sigma_c$. The paper defines $\mathcal S/\mathcal G$ as the accessible part $\mathrm{Ac}(\cdot)$ of the product; restricting to reachable states changes none of the three languages, so the product is run directly from $(x_0, q_0)$. The paper's standing assumption that $S$ is accessible is not a field of the structure; it appears as the hypothesis or conjunct `𝒮.S.Accessible` in every theorem.
-- source:
--   Ramadge and Wonham, Supervisory Control of a Class of Discrete Event Processes, SIAM J. Control Optim. 25(1), 1987, pp. 208–210, §2.2 (control patterns), §2.4 (supervisor, display (2.1), completeness); p. 211, display (3.1); p. 216, §6 (nonblocking, nonrejecting, proper)

import Mathlib
import Definitions.Def_RamadgeWonham_Shared_Generator

namespace RamadgeWonham.Shared

/-- A supervisor `𝒮 = (S, φ)` for a controlled generator with controllable events `Σ_c = Ec`
(§2.4, pp. 209–210): `S = (X, Σ, ξ, x₀, X_m)` is a deterministic automaton with (possibly infinite)
state set `X = S.Q` and partial transition function `ξ = S.δ`, and `φ : X → {0,1}^{Σ_c}` is the
state feedback map (`true` = enabled, `false` = disabled). -/
structure Supervisor (α : Type) (Ec : Set α) where
  /-- The supervisor's automaton `S = (X, Σ, ξ, x₀, X_m)`. -/
  S : Generator α
  /-- The state feedback map `φ : X → {0,1}^{Σ_c}`. -/
  φ : S.Q → Ec → Bool

namespace Supervisor

variable {α : Type} {Ec : Set α}

/-- `σ` is enabled at supervisor state `x`, i.e. `φ(x)(σ) = 1`, with `φ(x)` extended to `Σ` by
`φ(x)(σ) = 1` for `σ ∈ Σ − Σ_c` (p. 210). -/
def enabled (𝒮 : Supervisor α Ec) (x : 𝒮.S.Q) (σ : α) : Prop :=
  ∀ h : σ ∈ Ec, 𝒮.φ x ⟨σ, h⟩ = true

end Supervisor

variable {α : Type} {Ec : Set α}

open Classical in
/-- One step of the closed loop `ξ × δ_c` (p. 210): `(σ, x, q) ↦ (ξ(σ, x), δ(σ, q))`, defined iff
`δ(σ, q)` is defined, `φ(x)(σ) = 1`, and `ξ(σ, x)` is defined. -/
noncomputable def clStep (G : Generator α) (𝒮 : Supervisor α Ec) (σ : α)
    (p : 𝒮.S.Q × G.Q) : Option (𝒮.S.Q × G.Q) :=
  if 𝒮.enabled p.1 σ then
    match 𝒮.S.δ σ p.1, G.δ σ p.2 with
    | some x', some q' => some (x', q')
    | _, _ => none
  else none

/-- Extended transition function of the closed loop `𝒮/𝒢` from `(x₀, q₀)` (display (2.1), p. 210).
Taking the accessible part `Ac(·)` in (2.1) changes none of the languages below, so it is not built. -/
noncomputable def clRun (G : Generator α) (𝒮 : Supervisor α Ec) (s : List α) :
    Option (𝒮.S.Q × G.Q) :=
  s.foldl (fun o σ => o.bind (clStep G 𝒮 σ)) (some (𝒮.S.q0, G.q0))

/-- `L(𝒮/𝒢)`, the language generated by the closed loop (2.1). -/
def Lsup (G : Generator α) (𝒮 : Supervisor α Ec) : Set (List α) :=
  {s | (clRun G 𝒮 s).isSome}

/-- `L_m(𝒮/𝒢)`, the language marked by the closed loop (2.1), with marker set `X_m × Q_m`. -/
def Lmsup (G : Generator α) (𝒮 : Supervisor α Ec) : Set (List α) :=
  {s | ∃ x q, clRun G 𝒮 s = some (x, q) ∧ x ∈ 𝒮.S.Qm ∧ q ∈ G.Qm}

/-- The language controlled by `𝒮` in `𝒢`: `L_c(𝒮/𝒢) := L(𝒮/𝒢) ∩ L_m(𝒢)` (display (3.1), p. 211). -/
def Lcsup (G : Generator α) (𝒮 : Supervisor α Ec) : Set (List α) :=
  Lsup G 𝒮 ∩ G.Lm

/-- `𝒮` is complete with respect to `𝒢` (p. 210): for all `s ∈ Σ*`, `σ ∈ Σ`, if (i) `s ∈ L(𝒮/𝒢)`,
(ii) `sσ ∈ L(𝒢)`, (iii) `σ` is enabled at `ξ(s, x₀)`, then (iv) `sσ ∈ L(𝒮/𝒢)`. -/
def Complete (G : Generator α) (𝒮 : Supervisor α Ec) : Prop :=
  ∀ (s : List α) (σ : α), s ∈ Lsup G 𝒮 → s ++ [σ] ∈ G.L →
    (∀ x, 𝒮.S.run s = some x → 𝒮.enabled x σ) → s ++ [σ] ∈ Lsup G 𝒮

/-- `𝒮` is nonblocking: `L̄_c(𝒮/𝒢) = L(𝒮/𝒢)` (§6, p. 216). -/
def Nonblocking (G : Generator α) (𝒮 : Supervisor α Ec) : Prop :=
  pre (Lcsup G 𝒮) = Lsup G 𝒮

/-- `𝒮` is nonrejecting: `L̄_c(𝒮/𝒢) = L̄_m(𝒮/𝒢)` (§6, p. 216). -/
def Nonrejecting (G : Generator α) (𝒮 : Supervisor α Ec) : Prop :=
  pre (Lcsup G 𝒮) = pre (Lmsup G 𝒮)

/-- `𝒮` is proper: complete, nonblocking and nonrejecting (§6, p. 216), i.e. `𝒮` is complete and
`L̄_m(𝒮/𝒢) = L̄_c(𝒮/𝒢) = L(𝒮/𝒢)`. -/
def Proper (G : Generator α) (𝒮 : Supervisor α Ec) : Prop :=
  Complete G 𝒮 ∧ Nonblocking G 𝒮 ∧ Nonrejecting G 𝒮

end RamadgeWonham.Shared


