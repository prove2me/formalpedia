-- Prove2me | Definitions.Def_SparseCCE_ThreePlayer_Transcripts
-- name    : SparseCCE_ThreePlayer_Transcripts
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T05:06:05.635284+00:00
-- url     : https://prove2.me/theorems/4f96ee8d-dae0-4da6-a0e8-3e39937c405a
-- title:
--   Transcripts, simulation, causal laws, tests and causality errors, $\mathrm{enc}$, decodings, representation, repaired laws
-- statement:
--   A **transcript** of player $j$ is $z_j=(q_{j,1},\alpha_{j,1},\dots,q_{j,H},\alpha_{j,H})$ with $q_{j,1}\in Q_{j,1}=\Theta_j$, $q_{j,h}\in Q_{j,h}=O\times\Theta_j$ for $h\ge 2$ and answers $\alpha_{j,h}\in A_j$; $Z_j$ is the set of transcripts, $Z=\prod_jZ_j$, $M=\max_j|Z_j|$, $\lambda_j=\prod_h|Q_{j,h}|^{-1}$, $\lambda=\prod_j\lambda_j$, $\lambda_{>h}=\prod_j\prod_{\ell>h}|Q_{j,\ell}|^{-1}$. A play $\omega$ yields transcripts $z_j(\omega)$ recording $j$'s observations and actions.
--
--   **Simulation.** For $\pi\in\Delta(Z)$, $\tilde Q_\pi(\omega)=\mathrm{nat}(\omega)\pi(z(\omega))$ (eq. (3)); $V_j(z)=\sum_\omega\mathrm{nat}(\omega)\mathbf 1\{z(\omega)=z\}\Gamma_j(\omega)$ is $j$'s expected payoff, $0$ on a failed check. $E[F\mathbf 1_{S_h}]$ (`simPrefixExp`) is the same closed form for the first $h$ rounds: the simulation passes the checks of the first $h$ rounds and produces $u=(o_1,\dots,o_h)$ iff each $z_j$ begins with the query–answer pairs of $u$ and nature's moves are those of $u$.
--
--   **Tests.** A test of $j$ is $\kappa=(h,v,q)$ with $v$ a prefix of length $h-1$ and $q\in Q_{j,h}$; $f_\kappa(z_j)=\mathbf 1\{z_{j,<h}=v,q_{j,h}=q\}-\mathbf 1\{z_{j,<h}=v\}/|Q_{j,h}|$. For a joint law $\pi$ of $z_j$ and other transcripts $y$, $\mathrm{err}_j(\pi)=\sum_\kappa\sum_{\tilde y}|E_\pi[f_\kappa(z_j)\mathbf 1\{y=\tilde y\}]|$; $\delta_\pi=\sum_j\mathrm{err}_j(\pi)$. A law $p\in\Delta(Z_j)$ is **causal** if $E_p[f_\kappa]=0$ for every test.
--
--   **Encodings.** $\mathrm{enc}(x_j)(z)=\lambda_j\prod_h x_j(\alpha_h\mid\sigma,\theta)$ with $(\sigma,\theta)$ the observation recorded in the queries; a **decoding** of $p$ is a legal strategy that at each observation with $p(v,q)>0$ plays $p(\cdot\mid v,q)$ (arbitrary otherwise); $p$ **represents** $x_j$ if $p(z_j(\omega))=\lambda_j\prod_hx_j(a_{j,h}(\omega)\mid\sigma_h,\theta_{j,h}(\omega))$ for every play (eq. (4)). $p^c$ is a **repaired law** of $p$ if $p^c(z)=\lambda_j\prod_h c_h(\alpha_h\mid v_h,q_h)$ where $c_h$ is $p$'s conditional answer law where defined and an arbitrary distribution elsewhere.
--
--   For history-dependent protocols, the transcript entry for round $h$ records that round/history-specific signal, and the simulation uses the corresponding conditional nature probabilities.
-- source:
--   Fan Chen, Constantinos Daskalakis, Gabriele Farina, Noah Golowich and Charalampos Platanos, "On the Computation of Sparse Equilibria in Normal-Form Games", STOC 2027 submission (citation_basis: published; PDF SHA256 796c83067187974f1685ea4343c0c56d9f89e99484824615342fb7178ee023b5; PDF page = printed page). §3.3, eqs. (3)–(4), pp. 15–17; App. A.3, pp. 29–30.

import Mathlib
import Definitions.Def_SparseCCE_ThreePlayer_RepeatedGame

noncomputable section

namespace SparseCCE.ThreePlayer

open scoped BigOperators

namespace RepeatedGame

variable {ι : Type} [Fintype ι] [DecidableEq ι] (Γ : RepeatedGame ι)

/-! ### Transcripts (§3.3, pp. 15–16) -/

/-- A query of player `j`: an optional outcome of the previous round and a signal. The round-1
query is a signal only (`none`), the round-`h` query for `h ≥ 2` is a pair `(o, θ) ∈ O × Θ_j`. -/
abbrev Query (j : ι) := Option Γ.P.Outcome × Γ.P.Θ j

/-- A transcript `z_j = (q_{j,1}, α_{j,1}, …, q_{j,H}, α_{j,H})` of player `j`: one query
`q_{j,h} ∈ Q_{j,h}` and one answer `α_{j,h} ∈ A_j` per round, where `Q_{j,1} = Θ_j` and
`Q_{j,h} = O × Θ_j` for `h ≥ 2` (round `h` is index `h - 1` here). -/
def Transcript (j : ι) : Type :=
  {z : Fin Γ.H → Γ.Query j × Γ.P.A j // ∀ h, (z h).1.1 = none ↔ h.val = 0}

instance (j : ι) : Fintype (Γ.Transcript j) := by unfold Transcript; infer_instance
instance (j : ι) : DecidableEq (Γ.Transcript j) := by unfold Transcript; infer_instance

/-- `|Q_{j,h}|` for the round with index `h` (`|Θ_j|` in the first round, `|O| |Θ_j|` later). -/
def qCard (j : ι) (h : ℕ) : ℕ :=
  if h = 0 then Fintype.card (Γ.P.Θ j) else Fintype.card Γ.P.Outcome * Fintype.card (Γ.P.Θ j)

/-- `λ_j = ∏_h |Q_{j,h}|^{-1}` (p. 16). -/
def lam (j : ι) : ℝ := ∏ h : Fin Γ.H, (1 / (Γ.qCard j h.val : ℝ))

/-- `λ = ∏_j λ_j` (p. 16). -/
def lamTot : ℝ := ∏ j, Γ.lam j

/-- `λ_{>h} = ∏_j ∏_{ℓ > h} |Q_{j,ℓ}|^{-1}`, the probability that uniformly random queries pass
all checks after the first `h` rounds (p. 29–30); `h ∈ {0, …, H}`. -/
def lamAfter (h : ℕ) : ℝ :=
  ∏ j, ∏ ℓ : Fin Γ.H, if h ≤ ℓ.val then (1 / (Γ.qCard j ℓ.val : ℝ)) else 1

/-- `M = max_j |Z_j|` (p. 16). -/
def Mmax : ℕ := Finset.univ.sup (fun j => Fintype.card (Γ.Transcript j))

/-- The query–answer pair of player `j` in round `ℓ` of a (partial) play `u` of `h` rounds: the
outcome of the previous round (none in the first round) with the round's signal, and the
round's action. -/
def entry (j : ι) {h : ℕ} (u : Fin h → Γ.P.Outcome) (ℓ : Fin h) : Γ.Query j × Γ.P.A j :=
  ((if hℓ : ℓ.val = 0 then none else some (u ⟨ℓ.val - 1, by omega⟩), Γ.signalO ℓ.val (histOf u ℓ) j (u ℓ)),
    Γ.P.act j (u ℓ))

/-- The transcript `z_j(ω)` of player `j` in the play `ω`: its queries record the observations of
`j` in `ω` and its answers are its actions in `ω` (p. 16). -/
def trOf (ω : Γ.Play) (j : ι) : Γ.Transcript j :=
  ⟨fun h => Γ.entry j ω h, by
    intro h
    by_cases hh : h.val = 0 <;> simp [entry, hh]⟩

/-- Transcript profiles `z ∈ Z = ∏_j Z_j`. -/
abbrev TProfile := (j : ι) → Γ.Transcript j

/-- `z(ω) = (z_j(ω))_j`. -/
def playTr (ω : Γ.Play) : Γ.TProfile := fun j => Γ.trOf ω j

/-- The simulated law of play `Q̃_π(ω) = nat(ω) π(z(ω))` of a law `π ∈ Δ(Z)` of transcript
profiles (eq. (3), p. 16): the simulation passes all checks and produces `ω` iff `z = z(ω)` and
nature's moves are those of `ω`. -/
def simLaw (π : Γ.TProfile → ℝ) (ω : Γ.Play) : ℝ := Γ.nat ω * π (Γ.playTr ω)

/-- `V_j(z)`: the expected payoff of `j` in the simulation of `Γ` with the transcript profile `z`,
over nature's moves; it is `Γ_j(ω)` when the simulation produces `ω` and `0` when a check fails
(p. 16). -/
def simValue (j : ι) (z : Γ.TProfile) : ℝ :=
  ∑ ω : Γ.Play, Γ.nat ω * (if Γ.playTr ω = z then 1 else 0) * Γ.payoff j ω

/-- The first `h` query–answer pairs `z_{j,<h+1}` of a transcript (the prefix before the round with
index `h`). -/
def tPrefix {j : ι} (z : Γ.Transcript j) (h : Fin Γ.H) : Fin h.val → Γ.Query j × Γ.P.A j :=
  fun l => z.1 ⟨l.val, lt_trans l.isLt h.isLt⟩

/-- A prefix of length `h - 1` (p. 16): query–answer pairs for the rounds before round `h`, the
round-`ℓ` query in `Q_{j,ℓ}`. -/
def ValidPrefix {j : ι} {h : ℕ} (v : Fin h → Γ.Query j × Γ.P.A j) : Prop :=
  ∀ l : Fin h, (v l).1.1 = none ↔ l.val = 0

instance {j : ι} {h : ℕ} (v : Fin h → Γ.Query j × Γ.P.A j) : Decidable (Γ.ValidPrefix v) := by
  unfold ValidPrefix; infer_instance

/-- A test `κ = (h, v, q)` of player `j` (p. 17): a round `h`, a prefix `v` of length `h - 1`, and
a query `q ∈ Q_{j,h}`. -/
def Test (j : ι) : Type :=
  Σ h : Fin Γ.H, {v : Fin h.val → Γ.Query j × Γ.P.A j // Γ.ValidPrefix v} ×
    {q : Γ.Query j // q.1 = none ↔ h.val = 0}

instance (j : ι) : Fintype (Γ.Test j) := by unfold Test; infer_instance
instance (j : ι) : DecidableEq (Γ.Test j) := Classical.decEq _

/-- `f_κ(z_j) = 1{z_{j,<h} = v, q_{j,h} = q} − 1{z_{j,<h} = v} / |Q_{j,h}|` (p. 17). -/
def testFn {j : ι} (κ : Γ.Test j) (z : Γ.Transcript j) : ℝ :=
  (if Γ.tPrefix z κ.1 = κ.2.1.1 ∧ (z.1 κ.1).1 = κ.2.2.1 then 1 else 0) -
    (if Γ.tPrefix z κ.1 = κ.2.1.1 then 1 else 0) / (Γ.qCard j κ.1.val : ℝ)

/-- The causality error of `j` under a joint law `π` of `j`'s transcript and the transcripts
`y ∈ Y` of some other players (p. 17):
`err_j(π) = ∑_κ ∑_ỹ |E_π[f_κ(z_j) 1{z_{-j} = ỹ}]|`. -/
def err {j : ι} {Y : Type} [Fintype Y] (π : Γ.Transcript j → Y → ℝ) : ℝ :=
  ∑ κ : Γ.Test j, ∑ y : Y, |∑ z, π z y * Γ.testFn κ z|

/-- The causality error `err_j(p)` of a law `p ∈ Δ(Z_j)` of `j`'s transcript alone. -/
def errMarg {j : ι} (p : Γ.Transcript j → ℝ) : ℝ := Γ.err (fun z (_ : Unit) => p z)

/-- The transcripts of the players other than `j`. -/
abbrev Others (j : ι) := (i : {i : ι // i ≠ j}) → Γ.Transcript i.1

/-- The causality error `err_j(π)` of `j` under a law `π ∈ Δ(Z)` of transcript profiles. -/
def errProfile (j : ι) (π : Γ.TProfile → ℝ) : ℝ :=
  Γ.err (fun (z : Γ.Transcript j) (w : Γ.Others j) =>
    ∑ ζ : Γ.TProfile, if ζ j = z ∧ ∀ i : {i : ι // i ≠ j}, ζ i.1 = w i then π ζ else 0)

/-- `δ_π = ∑_j err_j(π)` (p. 17). -/
def deltaErr (π : Γ.TProfile → ℝ) : ℝ := ∑ j, Γ.errProfile j π

/-- A law `p ∈ Δ(Z_j)` is causal: in every round the query is uniform on `Q_{j,h}` and
independent of the prefix, i.e. `E_p[f_κ] = 0` for every test `κ` of `j` (pp. 16–17). -/
def IsCausal {j : ι} (p : Γ.Transcript j → ℝ) : Prop := ∀ κ : Γ.Test j, ∑ z, p z * Γ.testFn κ z = 0

/-- The uniform law `unif_j` on `Z_j`. -/
def unifLaw (j : ι) : Γ.Transcript j → ℝ := fun _ => 1 / (Fintype.card (Γ.Transcript j) : ℝ)

/-- `p(v, q)`: the probability under `p` that the transcript begins with the prefix `v` followed by
the round-`h` query `q` (p. 29). -/
def probPQ {j : ι} (p : Γ.Transcript j → ℝ) (h : Fin Γ.H) (v : Fin h.val → Γ.Query j × Γ.P.A j)
    (q : Γ.Query j) : ℝ :=
  ∑ z, if Γ.tPrefix z h = v ∧ (z.1 h).1 = q then p z else 0

/-- The probability under `p` that the transcript begins with `v`, then the round-`h` query `q`
and the round-`h` answer `a`. -/
def probPQA {j : ι} (p : Γ.Transcript j → ℝ) (h : Fin Γ.H) (v : Fin h.val → Γ.Query j × Γ.P.A j)
    (q : Γ.Query j) (a : Γ.P.A j) : ℝ :=
  ∑ z, if Γ.tPrefix z h = v ∧ z.1 h = (q, a) then p z else 0

/-- The prefix `v(σ)` of length `h - 1` determined by a round-`h` history `σ` of player `j`. -/
def obsPrefix (j : ι) (h : Fin Γ.H) (σ : Fin h.val → Γ.P.Outcome) :
    Fin h.val → Γ.Query j × Γ.P.A j := Γ.entry j σ

/-- The round-`h` query `q(σ, θ)` determined by a round-`h` observation `(σ, θ)`. -/
def obsQuery (j : ι) (h : Fin Γ.H) (σ : Fin h.val → Γ.P.Outcome) (θ : Γ.P.Θ j) : Γ.Query j :=
  (if hh : h.val = 0 then none else some (σ ⟨h.val - 1, by omega⟩), θ)

/-- `x` is a decoding of `p` (p. 16, p. 29): a legal strategy that, at every round-`h`
observation `(σ, θ)` whose prefix and query have positive probability under `p`, draws its
action from the conditional law `p(· | v(σ), q(σ, θ))` of the round-`h` answer; at
probability-zero pairs it is arbitrary ("arbitrarily if they have probability zero"). -/
def IsDecoding {j : ι} (p : Γ.Transcript j → ℝ) (x : Γ.Strategy j) : Prop :=
  Γ.IsLegal x ∧ ∀ h σ θ a, 0 < Γ.probPQ p h (Γ.obsPrefix j h σ) (Γ.obsQuery j h σ θ) →
    x h σ θ a = Γ.probPQA p h (Γ.obsPrefix j h σ) (Γ.obsQuery j h σ θ) a /
      Γ.probPQ p h (Γ.obsPrefix j h σ) (Γ.obsQuery j h σ θ)

/-- The history recorded in the first `h` queries of a transcript: the outcome of round `l` is
recorded in the query of round `l + 1`. -/
def recHist {j : ι} (z : Γ.Transcript j) (h : Fin Γ.H) : Fin h.val → Γ.P.Outcome :=
  fun l => Option.get (z.1 ⟨l.val + 1, by omega⟩).1.1 (by
    rcases hz : (z.1 ⟨l.val + 1, by omega⟩).1.1 with _ | o
    · exact absurd ((z.2 _).1 hz) (by simp)
    · simp)

/-- The causal law `enc(x_j)` of a legal strategy (p. 16): in every round it draws a uniform query,
independently of the earlier entries, and then an answer from `x_j(· | σ, θ)`, `(σ, θ)` being the
round-`h` observation recorded in the queries drawn so far:
`enc(x_j)(z) = λ_j ∏_h x_j(α_h | σ, θ)`. -/
def encLaw {j : ι} (x : Γ.Strategy j) : Γ.Transcript j → ℝ :=
  fun z => Γ.lam j * ∏ h, x h (Γ.recHist z h) (z.1 h).1.2 (z.1 h).2

/-- `p ∈ Δ(Z_j)` represents the legal strategy `x_j` (eq. (4), p. 16):
`p(z_j(ω)) = λ_j ∏_h x_j(a_{j,h}(ω) | σ_h, θ_{j,h}(ω))` for every play `ω`. -/
def Represents {j : ι} (p : Γ.Transcript j → ℝ) (x : Γ.Strategy j) : Prop :=
  ∀ ω : Γ.Play, p (Γ.trOf ω j) =
    Γ.lam j * ∏ h, x h (Γ.hist ω h) (Γ.signalO h.val (Γ.hist ω h) j (ω h)) (Γ.P.act j (ω h))

/-- `pc` is the repaired law `p^c` of `p` (Lemma A.2, p. 30): every query is drawn uniformly and
every answer from the conditional answer law of `p`, `p^c(z) = λ_j ∏_h p(α_h | v_h, q_h)`; at
prefix–query pairs of probability zero the answer law `c` is an arbitrary distribution. -/
def IsRepair {j : ι} (p pc : Γ.Transcript j → ℝ) : Prop :=
  ∃ c : (h : Fin Γ.H) → (Fin h.val → Γ.Query j × Γ.P.A j) → Γ.Query j → Γ.P.A j → ℝ,
    (∀ h v q, IsDist (c h v q)) ∧
    (∀ h v q a, 0 < Γ.probPQ p h v q → c h v q a = Γ.probPQA p h v q a / Γ.probPQ p h v q) ∧
    ∀ z, pc z = Γ.lam j * ∏ h, c h (Γ.tPrefix z h) (z.1 h).1 (z.1 h).2

/-- `E[F 1_{S_h}]` for the simulation run with transcripts `z ∼ π` (pp. 29–30): `S_h` is the event
that the simulation passes all checks of the first `h` rounds, and `F` is a payoff determined
by the first `h` outcomes. The simulation passes these checks and produces the outcomes
`u = (o_1, …, o_h)` iff every `z_j` begins with the query–answer pairs of `u` and nature's
moves are those of `u`. -/
def simPrefixExp (π : Γ.TProfile → ℝ) (h : Fin (Γ.H + 1)) (F : (Fin h.val → Γ.P.Outcome) → ℝ) :
    ℝ :=
  ∑ ζ : Γ.TProfile, π ζ * ∑ u : Fin h.val → Γ.P.Outcome,
    (∏ l, Γ.natO l.val (histOf u l) (u l)) *
      (if ∀ j (l : Fin h.val), (ζ j).1 ⟨l.val, by omega⟩ = Γ.entry j u l then 1 else 0) * F u

end RepeatedGame

end SparseCCE.ThreePlayer


