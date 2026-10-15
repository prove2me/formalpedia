-- Prove2me | Definitions.Def_OAI_Probability_Ising_Covariance
-- name    : OAI_Probability_Ising_Covariance
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T22:01:36.25171+00:00
-- url     : https://prove2.me/theorems/1fdc6809-2393-40d6-9ea5-71bdc0765bb4
-- title:
--   Two-spin covariance, terminal tilts and the effective-coupling bound
-- statement:
--   Let $w:\{-1,+1\}^2\to\mathbb{R}$ be a two-spin table with expectation $\mathbb{E}_w[f]=\sum_{s,t}w(s,t)f(s,t)\big/\sum_{s,t}w(s,t)$ and effective coupling $K(w)=\frac14\bigl(\log w(+,+)+\log w(-,-)-\log w(+,-)-\log w(-,+)\bigr)$. The file introduces:
--
--   1. **Table covariance.** $\operatorname{Cov}(w)=\mathbb{E}_w[st]-\mathbb{E}_w[s]\,\mathbb{E}_w[t]$, the covariance of the two spins under the normalized table.
--
--   2. **Terminal tilt.** For $A,B\in\mathbb{R}$, the table $w^{A,B}(s,t)=w(s,t)\,e^{As+Bt}$.
--
--   3. **Adding terminal fields.** For a field $h\in\mathbb{R}^n$, sites $u,v$ and $A,B\in\mathbb{R}$, the field $\bigl(h+A\delta_u+B\delta_v\bigr)_x=h_x+A\,\mathbf{1}[x=u]+B\,\mathbf{1}[x=v]$; when $u=v$ both increments land on the same site.
--
--   4. **Effective-coupling bound.** The proposition that for every finite ferromagnetic graph $G$ on $V=\{0,\dots,n-1\}$ (any $n,m$, couplings $K_e\ge0$, no loops), every field $h\in\mathbb{R}^V$ and all distinct sites $u\neq v$,
--
--      $$K\bigl(T_{w_h,u,v}\bigr)\le K\bigl(T_{w_0,u,v}\bigr),$$
--
--      where $w_h$ is the Ising weight of $G$ with field $h$ and $T_{W,u,v}(s,t)=\sum_{\sigma:\,\sigma_u=s,\,\sigma_v=t}W(\sigma)$ is the two-spin marginal table at $u,v$.
--
--   The effective-coupling bound says that external fields never increase the effective interaction between two sites of a ferromagnet. Tilting a positive table by terminal fields leaves $K$ unchanged, and the covariance of a positive table with $w(+,+)w(-,-)\ge w(+,-)w(-,+)$ is at most $\tanh K(w)$; these facts are used to show that the bound is equivalent to the arbitrary-field covariance bound $\langle\sigma_u\sigma_v\rangle_h-\langle\sigma_u\rangle_h\langle\sigma_v\rangle_h\le\langle\sigma_u\sigma_v\rangle_0$.
--
--   **Formalization Note** The Lean names are `tableCovariance`, `tiltTable`, `addTerminalFields h u v A B` and `EffectiveCouplingBound`; in the latter the pair table is `pairTable (weight G h) u v` and $K$ is `tableCoupling`. `EffectiveCouplingBound` is a `Prop` and requires $u\neq v$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Ising/Covariance.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/Ising/Covariance.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BufferedIsing mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BufferedIsing
import Definitions.Def_OAI_Probability_Ising_Basic
import Definitions.Def_OAI_Probability_Ising_Colorings
import Definitions.Def_OAI_Probability_Ising_EdwardsSokal
import Definitions.Def_OAI_Probability_Ising_TwoSpin
import Definitions.Def_OAI_Probability_Ising_SpinCorrelation
import Definitions.Def_OAI_Probability_Ising_Marginals
import Definitions.Def_OAI_Probability_Ising_PinnedMarginal

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open scoped BigOperators Classical

namespace BufferedIsing

/-- Covariance of the two canonical spins of a positive two-spin table. -/
noncomputable def tableCovariance (w : Bool → Bool → ℝ) : ℝ :=
  tableExpectation w (fun s t => spin s * spin t) -
    tableExpectation w (fun s _ => spin s) *
      tableExpectation w (fun _ t => spin t)

/-- Multiplying by terminal fields does not change the effective interaction. -/
noncomputable def tiltTable (w : Bool → Bool → ℝ) (A B : ℝ) (s t : Bool) : ℝ :=
  w s t * Real.exp (A * spin s + B * spin t)

/-- Actual addition of two (possibly mixed-sign) finite external fields. -/
def addTerminalFields {n : ℕ} (h : Fin n → ℝ) (u v : Fin n) (A B : ℝ)
    (x : Fin n) : ℝ := h x + (if x = u then A else 0) + (if x = v then B else 0)

/-- External fields do not increase the two-terminal effective coupling. -/
def EffectiveCouplingBound : Prop :=
  ∀ (n m : ℕ) (G : FiniteGraph n m) (h : Fin n → ℝ) (u v : Fin n), u ≠ v →
    tableCoupling (pairTable (weight G h) u v) ≤
      tableCoupling (pairTable (weight G (fun _ => 0)) u v)

end BufferedIsing

end OAI


