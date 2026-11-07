-- Prove2me | Definitions.Def_RegevRecon_qLaw
-- name    : RegevRecon_qLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:03:43.195195+00:00
-- url     : https://prove2.me/theorems/59ef808f-e704-4b30-b908-7eb0a419d7c5
-- title:
--   BPQM density evolution: the laws $\mathcal Q_\ell$, $v^{(\ell)}$, $\mu_{\mathrm{root}}^{(\ell)}$, $P_{\mathrm{err}}^{(\ell)}$ and the threshold $\beta_{\mathrm{BPQM}}$
-- statement:
--   **Quantum density evolution** tracks the classical part of the BPQM messages. Start from $q^{(0)}=e_0$. One round has two updates.
--
--   1. Equality update at a symbol: $v^{(\ell)}=\mu*q_1^{(\ell)}*\dots*q_{k-1}^{(\ell)}$ with independent $q_h^{(\ell)}$ (35).
--   2. Parity update at a check: draw $(c_0,\dots,c_{D-1})\sim\Lambda$, set $\gamma_t=c_t/c_0$, take independent incoming $v_1,\dots,v_{D-1}$, relabel $\nu_{t,a}=v_{t,-\gamma_ta}$, draw $s=(s_2,\dots,s_{D-1})$ with $s_1=0$ with probability
--
--   $$
--   Z_s=\sum_a\prod_{t=1}^{D-1}\nu_{t,a+s_t},\qquad\text{and output}\qquad q_a^{(\ell+1)}=\frac{\prod_t\nu_{t,a+s_t}}{Z_s}.
--   $$
--
--   The root combines $k$ independent messages, $\mu_{\mathrm{root}}^{(\ell)}=\mu*q_1^{(\ell)}*\dots*q_k^{(\ell)}$, with average error $P_{\mathrm{err}}^{(\ell)}=E[P_{\mathrm{err}}(\mu_{\mathrm{root}}^{(\ell)})]$ (39). The decoding threshold is
--
--   $$
--   \beta_{\mathrm{BPQM}}=\inf\{\beta>0:\lim_{\ell\to\infty}P_{\mathrm{err}}^{(\ell)}>0\}\qquad(52).
--   $$
--
--   **Formalization Note** A branch with $Z_s=0$ has mass zero, so its normalization is never read. The threshold takes values in $[0,\infty]$, and "$\lim>0$" is the negation of convergence to $0$; the limit exists by a milestone.
-- source:
--   Jordan, Nguyen, Zhou, Regev's Reduction Reaches Reconstruction, STOC 2027 submission (manuscript sha256 9f861d6a…), §5, (35)–(39), pp.13–14; (52), p.21

import Mathlib
import Definitions.Def_RegevRecon_Messages

namespace RegevRecon

open Finset Filter Topology

variable {p : ℕ} [Fact p.Prime]

/-- The outcome string `(s_1, …, s_{D−1})` with `s_1 = 0` from `(s_2, …, s_{D−1}) ∈ F_p^{D−2}`, p.14. -/
def fullOutcome {D : ℕ} (s : Fin (D - 2) → ZMod p) (t : Fin (D - 1)) : ZMod p :=
  if h : t.val = 0 then 0 else s ⟨t.val - 1, by have := t.isLt; omega⟩

/-- `Z_s = Σ_a Π_t ν_{t,a+s_t}`, (36), p.14. -/
noncomputable def checkWeight {D : ℕ} (ν : Fin (D - 1) → Vec p) (s : Fin (D - 2) → ZMod p) : ℝ :=
  ∑ a, ∏ t, ν t (a + fullOutcome s t)

/-- The outgoing check vector `q_a = Π_t ν_{t,a+s_t} / Z_s`, (37), p.14. Only read with the weight
`Z_s`, as (37) requires `Z_s > 0`. -/
noncomputable def checkOut {D : ℕ} (ν : Fin (D - 1) → Vec p) (s : Fin (D - 2) → ZMod p) : Vec p :=
  fun a => (∏ t, ν t (a + fullOutcome s t)) / checkWeight ν s

/-- One equality update, (35), p.13: the law of `v = μ ∗ q_1 ∗ ⋯ ∗ q_{k−1}` for independent
`q_h ∼ P`. -/
noncomputable def symbolStep (k : ℕ) (μ : Vec p) (P : Law (Vec p)) : Law (Vec p) :=
  (Law.iid (k - 1) P).map (convAll μ)

/-- One parity update, (36)–(37), p.14, with `α_t = −γ_t` (p.23): draw `c ∼ Λ`, independent incoming
`v_1, …, v_{D−1} ∼ Pv`, relabel `ν_t = R_{α_t} v_t`, draw `s` with probability `Z_s`, output (37). -/
noncomputable def checkStep {D : ℕ} (Λ : PMF (Fin D → (ZMod p)ˣ)) (Pv : Law (Vec p)) :
    Law (Vec p) :=
  (coeffLaw Λ).bind fun c => (Law.iid (D - 1) Pv).bind fun vs =>
    let ν : Fin (D - 1) → Vec p := fun t => relabel (-gammaRatio c t) (vs t)
    Law.ofWeights (checkWeight ν) (checkOut ν)

/-- **The BPQM check-to-symbol law `𝒬_ℓ`** of quantum density evolution, Jordan, Nguyen, Zhou, *Regev's Reduction Reaches Reconstruction*, STOC 2027 submission (manuscript sha256 9f861d6a…), §5, (35)–(38),
p.14, with the unshifted physical channel `μ` of (41) (p.21).

**Formalization Note** A law is the finitely supported `Law`, so `Z_s = 0` branches have mass zero
and their normalization is never read. Exchangeability of `Λ` is a hypothesis of the theorems, not
of this definition. -/
noncomputable def qLaw (k D : ℕ) (S : Finset (ZMod p)) (Λ : PMF (Fin D → (ZMod p)ˣ)) (β : ℝ) :
    ℕ → Law (Vec p)
  | 0 => Law.dirac e0
  | ℓ + 1 => checkStep Λ (symbolStep k (channel S β) (qLaw k D S Λ β ℓ))

/-- The symbol-to-check law of `v^(ℓ)`, (35), p.13; `v^(0) = μ`. -/
noncomputable def vLaw (k D : ℕ) (S : Finset (ZMod p)) (Λ : PMF (Fin D → (ZMod p)ˣ)) (β : ℝ)
    (ℓ : ℕ) : Law (Vec p) :=
  symbolStep k (channel S β) (qLaw k D S Λ β ℓ)

/-- The law of `μ_root^(ℓ) = μ ∗ q_1 ∗ ⋯ ∗ q_k`, (39), p.14, with `k` independent inputs. -/
noncomputable def rootLaw (k D : ℕ) (S : Finset (ZMod p)) (Λ : PMF (Fin D → (ZMod p)ˣ)) (β : ℝ)
    (ℓ : ℕ) : Law (Vec p) :=
  (Law.iid k (qLaw k D S Λ β ℓ)).map (convAll (channel S β))

/-- The average terminal error `P_err^(ℓ) = E[P_err(μ_root^(ℓ))]`, (39), p.14. -/
noncomputable def perr (k D : ℕ) (S : Finset (ZMod p)) (Λ : PMF (Fin D → (ZMod p)ˣ)) (β : ℝ)
    (ℓ : ℕ) : ℝ :=
  (rootLaw k D S Λ β ℓ).expect pErr

/-- The second moment `m_ℓ(b) = E[|q̂^(ℓ)(b)|²]`, p.23. -/
noncomputable def secondMoment (k D : ℕ) (S : Finset (ZMod p)) (Λ : PMF (Fin D → (ZMod p)ˣ)) (β : ℝ)
    (ℓ : ℕ) (b : ZMod p) : ℝ :=
  (qLaw k D S Λ β ℓ).expect fun q => ‖fourier q b‖ ^ 2

/-- **The BPQM decoding threshold**, (52), p.21:
`β_BPQM = inf {β > 0 : lim_{ℓ→∞} P_err^(ℓ) > 0}`.

**Formalization Note** The threshold lives in `ℝ≥0∞`, so `inf ∅ = ∞`. "`lim > 0`" is the negation of
convergence to `0`: for a nonnegative sequence with a limit these agree, and the limit exists by
milestone `error_limit_exists`. -/
noncomputable def betaBPQM (k D : ℕ) (S : Finset (ZMod p)) (Λ : PMF (Fin D → (ZMod p)ˣ)) :
    ENNReal :=
  sInf (ENNReal.ofReal '' {β : ℝ | 0 < β ∧ ¬ Tendsto (perr k D S Λ β) atTop (𝓝 0)})

end RegevRecon


