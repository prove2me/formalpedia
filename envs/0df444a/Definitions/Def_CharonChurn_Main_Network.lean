-- Prove2me | Definitions.Def_CharonChurn_Main_Network
-- name    : CharonChurn_Main_Network
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T00:55:44.561023+00:00
-- url     : https://prove2.me/theorems/678a276c-971e-4768-a5cc-243583479e23
-- title:
--   Dynamic network, standing assumptions, persistent graph $G^*$ and the horizon $L_{\mathrm{flood}}$
-- statement:
--   Public parameters are naturals $n,D,t,c,\tau$ and a real $\hat\lambda_0$. Process identities are natural numbers (an unbounded identity supply); a network gives, for each round $r$, the finite set $V_r$ of present identities and the physical graph $G_r$, together with the fixed Byzantine set $B$ and the session identifier active in round $r$.
--
--   * Parameter assumptions: $\tau\ge1$, $0<\hat\lambda_0\le1$, $D>4(t+c)$.
--   * Round $r$ assumptions: $|V_r|=n$, $B\subseteq V_r$, edges only between present processes, $G_r[V_r]$ is $D$-regular with normalized absolute spectral gap at least $\hat\lambda_0$, and $\kappa(G_r[V_r])>2(t+c)$.
--   * Churn: at most $c$ identities leave between rounds $r$ and $r+1$ (equally many join, since $|V_r|=n$; Byzantine identities never leave).
--   * Identity and session model: an identity that leaves never returns (so joining identities are fresh), and a session identifier once replaced is never reused.
--   * $|B|\le t$. *Admissible* bundles all of these, in every round.
--
--   $C_r=V_r\setminus B$. For a window $[s,e]$ the persistent vertex set is $V^*=\bigcap_{q=s}^eV_q$ and $\{u,v\}$ is a persistent edge iff it is a physical edge in every round of the window; $\kappa(G^*)$ is the connectivity of this graph on $V^*$ (no connectivity, regularity or nonemptiness is imposed on it). Finally $L_{\mathrm{flood}}(n,\hat\lambda_0)=2\lceil4/\hat\lambda_0\rceil+\lceil6\ln n/\hat\lambda_0\rceil+\lceil4\ln n/\hat\lambda_0\rceil+4$ and $\Gamma=\tau+L_{\mathrm{flood}}$ (also the retention horizon $F_{\mathrm{ret}}$).
-- source:
--   Sengupta and Perrin (2026), Byzantine Partition Detection Under Churn, supplied 48-page artifact (venue metadata: STOC 2027 submission; citation basis published per source.meta.json; SHA-256 3f9994406f38c73927d0b5cc78d0dd05740de0f7d09e544b7b203eefe39cdb74), §§2.1–2.7, pp. 7–11 (PDF 7–11), Definition 2 p. 8; Theorem 12 (horizon), p. 22; §3.1 (Γ, F_ret), p. 12

import Mathlib
import Definitions.Def_CharonChurn_Main_Connectivity
import Definitions.Def_CharonChurn_Main_SpectralGap

namespace CharonChurn.Main

/-! # The dynamic network, its standing assumptions, the persistent graph and `L_flood`
(Sengupta–Perrin 2026, §§2.1–2.7, pp. 7–11; Theorem 12, p. 22) -/

/-- Public parameters: `n` processes per round, degree `D`, Byzantine bound `t`, churn bound `c`,
window length `τ` and the spectral-gap lower bound `lam = λ̂₀`. -/
structure Params where
  n : ℕ
  D : ℕ
  t : ℕ
  c : ℕ
  τ : ℕ
  lam : ℝ

/-- A dynamic network. Process identities are natural numbers: an unbounded supply of identities,
of which round `r` uses the finite set `V r`. `G r` is the physical graph of round `r` (only its
restriction to `V r` matters), `B` the fixed Byzantine set, and `session r` the session
identifier supplied by the execution model in round `r`. -/
structure Network where
  V : ℕ → Finset ℕ
  G : ℕ → SimpleGraph ℕ
  B : Finset ℕ
  session : ℕ → ℕ

/-- Parameter assumptions: `τ ≥ 1`, `0 < λ̂₀ ≤ 1`, `D > 4(t + c)`. -/
structure ParamsOK (P : Params) : Prop where
  tau_pos : 1 ≤ P.τ
  lam_pos : 0 < P.lam
  lam_le_one : P.lam ≤ 1
  degree_bound : 4 * (P.t + P.c) < P.D

/-- Assumptions on the instantaneous graph of round `r`: exactly `n` processes, every Byzantine
identity present, edges only between present processes, `D`-regular, normalized absolute spectral
gap at least `λ̂₀`, and vertex connectivity greater than `2(t + c)`. -/
structure RoundOK (P : Params) (N : Network) (r : ℕ) : Prop where
  card_eq : (N.V r).card = P.n
  byz_present : N.B ⊆ N.V r
  edges_inside : ∀ u v, (N.G r).Adj u v → u ∈ N.V r ∧ v ∈ N.V r
  regular : IsRegularOn (N.G r) (N.V r) P.D
  gap : HasAbsGapAtLeast (N.G r) (N.V r) P.D P.lam
  connectivity : 2 * (P.t + P.c) < kappa (N.G r) (N.V r)

/-- Churn bound for the transition `r → r + 1`: at most `c` processes leave (and, the round sizes
being equal, the same number join). Byzantine processes never leave by `RoundOK.byz_present`. -/
def ChurnOK (P : Params) (N : Network) (r : ℕ) : Prop :=
  (N.V r \ N.V (r + 1)).card ≤ P.c

/-- Identity and session model: an identity that leaves never returns (so joining identities are
fresh), and a session identifier, once replaced, is never used again. -/
structure IdModel (N : Network) : Prop where
  no_reuse : ∀ a m b v, a ≤ m → m ≤ b → v ∈ N.V a → v ∈ N.V b → v ∈ N.V m
  session_fresh : ∀ a m b, a ≤ m → m ≤ b → N.session a = N.session b → N.session m = N.session a

/-- All standing network, Byzantine-fault and churn assumptions, in every round. -/
structure Admissible (P : Params) (N : Network) : Prop where
  params : ParamsOK P
  byz_card : N.B.card ≤ P.t
  round : ∀ r, RoundOK P N r
  churn : ∀ r, ChurnOK P N r
  ids : IdModel N

/-- Correct processes of round `r`: `C_r = V_r \ B`. -/
def correctSet (N : Network) (r : ℕ) : Finset ℕ := N.V r \ N.B

/-- Persistent vertex set `V*` of the window `[s, e]`: identities present in every round. -/
noncomputable def persistV (N : Network) (s e : ℕ) : Finset ℕ := by
  classical
  exact (N.V s).filter (fun v => ∀ q ∈ Finset.Icc s e, v ∈ N.V q)

/-- Persistent graph: `{u, v}` is an edge iff it is a physical edge in every round of `[s, e]`
(an intersection of the snapshots, not a union). Its vertex set is `persistV N s e`. -/
def persistG (N : Network) (s e : ℕ) : SimpleGraph ℕ where
  Adj u v := u ≠ v ∧ ∀ q ∈ Finset.Icc s e, (N.G q).Adj u v
  symm := ⟨fun _ _ h => ⟨h.1.symm, fun q hq => (h.2 q hq).symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- `κ(G*)` of the window `[s, e]`. -/
noncomputable def kappaStar (N : Network) (s e : ℕ) : ℕ :=
  kappa (persistG N s e) (persistV N s e)

/-- The deterministic dissemination horizon of Theorem 12:
`L_flood = 2⌈4/λ̂₀⌉ + ⌈6 ln n / λ̂₀⌉ + ⌈4 ln n / λ̂₀⌉ + 4`. -/
noncomputable def Lflood (n : ℕ) (lam : ℝ) : ℕ :=
  2 * ⌈4 / lam⌉₊ + ⌈6 * Real.log n / lam⌉₊ + ⌈4 * Real.log n / lam⌉₊ + 4

/-- Observation-plus-dissemination horizon `Γ = τ + L_flood`, also the retention horizon
`F_ret = Γ`. -/
noncomputable def Gamma (P : Params) : ℕ := P.τ + Lflood P.n P.lam

end CharonChurn.Main


