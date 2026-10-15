-- Prove2me | Definitions.Def_OAI_Probability_Ising_FieldUpdate
-- name    : OAI_Probability_Ising_FieldUpdate
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T22:07:30.994508+00:00
-- url     : https://prove2.me/theorems/a8b16ed0-ff63-4e6d-adf9-d1642aa1d7f1
-- title:
--   Fixing a single spin: inserted configurations, induced fields, conditional magnetizations and single-site field increments
-- statement:
--   Let $V$ be a finite set, $J=(J_{uv})$ a real coupling array and $h\in\mathbb{R}^V$ a field, with Ising Hamiltonian $\mathcal H_{J,h}(\sigma)=\sum_{u,w\in V}J_{uw}\sigma_u\sigma_w+\sum_u h_u\sigma_u$, mass $\mu_{J,h}=e^{\mathcal H_{J,h}}$, partition function $Z_{J,h}$, averages $\langle\cdot\rangle_{J,h}$ and magnetizations $m_o(J,h)=\langle\sigma_o\rangle_{J,h}$. Fix a site $v\in V$ and a spin value $b\in\{-1,+1\}$, and write $V'=V\setminus\{v\}$. The file defines:
--
--   1. **Inserted configuration.** For $\eta\in\{-1,+1\}^{V'}$, the configuration $b\oplus_v\eta\in\{-1,+1\}^V$ equal to $b$ at $v$ and to $\eta$ on $V'$.
--
--   2. **Removed field and removed coupling.** The field on $V'$ induced by the fixed spin, and the restriction of $J$ to $V'$:
--
--      $$h^{(v,b)}_u=h_u+(J_{vu}+J_{uv})\,b,\qquad J^{(v)}_{uw}=J_{uw}\qquad(u,w\in V').$$
--
--   3. **Pinned mean.** For $o\in V$, $m^{(v,b)}_o=\bigl\langle (b\oplus_v\eta)_o\bigr\rangle_{J^{(v)},h^{(v,b)}}$, the average over $\eta$ in the model on $V'$; it is the conditional magnetization at $o$ given $\sigma_v=b$, and equals $b$ when $o=v$.
--
--   4. **Pinned partition function.** $Z^{(v,b)}=e^{J_{vv}+h_v b}\,Z_{J^{(v)},h^{(v,b)}}$, the total mass of the configurations with $\sigma_v=b$.
--
--   5. **Single-site field.** For $t\in\mathbb{R}$, the field $t\,\delta_v$ equal to $t$ at $v$ and $0$ elsewhere.
--
--   6. **Global spin flip.** The involution $\sigma\mapsto-\sigma$ of $\{-1,+1\}^V$.
--
--   These objects express conditioning on one spin exactly: $\mathcal H_{J,h}(b\oplus_v\eta)=J_{vv}+h_vb+\mathcal H_{J^{(v)},h^{(v,b)}}(\eta)$, so the partition function splits as $Z_{J,h}=Z^{(v,+1)}+Z^{(v,-1)}$ and every magnetization is the corresponding mixture of pinned means. Adding a field $t\delta_v$ only reweights the two pinned parts by $e^{\pm t}$, which leads to the update rule $m_v(J,h+t\delta_v)=\frac{m_v(J,h)+\tanh t}{1+m_v(J,h)\tanh t}$, and the spin flip yields the symmetry $m_o(J,-h)=-m_o(J,h)$. Together these are the tools of the inductive proof of the influence bound.
--
--   **Formalization Note** The definitions are in the namespace `OAI.BufferedIsing.DSS`: `insertSpin`, `removedField`, `removedCoupling`, `pinMean`, `pinPart`, `fieldAt` and `flipEquiv`, with the simp lemmas `insertSpin_self`, `insertSpin_other`, `fieldAt_self`, `fieldAt_other` and `fieldAt_zero`. The remaining sites form the subtype `{u // u ≠ v}`, and `insertSpin` is built from `Equiv.funSplitAt`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Ising/FieldUpdate.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/Ising/FieldUpdate.lean by skeleton subtraction
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
import Definitions.Def_OAI_Probability_Ising_Covariance
import Definitions.Def_OAI_Probability_Ising_Contraction
import Definitions.Def_OAI_Probability_Ising_GibbsMeasure
import Definitions.Def_OAI_Probability_Ising_Interpolation

namespace OAI

open scoped BigOperators Classical

namespace BufferedIsing.DSS

noncomputable section

variable {V : Type*} [Fintype V]

/-- The spin at the removed site is inserted without discarding any edge interaction. -/
def insertSpin (v : V) (b : Bool) (η : {u : V // u ≠ v} → Bool) : V → Bool :=
  (Equiv.funSplitAt v Bool).symm (b, η)

omit [Fintype V] in
@[simp] lemma insertSpin_self (v : V) (b : Bool) (η : {u : V // u ≠ v} → Bool) :
    insertSpin v b η v = b := by simp [insertSpin, Equiv.funSplitAt, Equiv.piSplitAt]

omit [Fintype V] in
@[simp] lemma insertSpin_other (v : V) (b : Bool) (η : {u : V // u ≠ v} → Bool)
    (u : {u : V // u ≠ v}) : insertSpin v b η u = η u := by
  simp [insertSpin, Equiv.funSplitAt, Equiv.piSplitAt, u.property]

/-- Conditional field induced by an actual fixed spin. -/
def removedField (J : V → V → ℝ) (h : V → ℝ) (v : V) (b : Bool)
    (u : {u : V // u ≠ v}) : ℝ := h u + (J v u + J u v) * sgn b

def removedCoupling (J : V → V → ℝ) (v : V)
    (u w : {u : V // u ≠ v}) : ℝ := J u w

/-- Conditional mean at a fixed-spin site; defined on actual remaining spins. -/
def pinMean (J : V → V → ℝ) (h : V → ℝ) (v : V) (b : Bool) (o : V) : ℝ :=
  average (removedCoupling J v) (removedField J h v b) (fun η => sgn (insertSpin v b η o))

def pinPart (J : V → V → ℝ) (h : V → ℝ) (v : V) (b : Bool) : ℝ :=
  Real.exp (J v v + h v * sgn b) * part (removedCoupling J v) (removedField J h v b)

/-- A single finite field increment. -/
def fieldAt (v : V) (t : ℝ) : V → ℝ := fun u => if u = v then t else 0

omit [Fintype V] in
@[simp] lemma fieldAt_self (v : V) (t : ℝ) : fieldAt v t v = t := by simp [fieldAt]

omit [Fintype V] in
@[simp] lemma fieldAt_other (v : V) (t : ℝ) (u : V) (hu : u ≠ v) :
    fieldAt v t u = 0 := by simp [fieldAt, hu]

def flipEquiv : (V → Bool) ≃ (V → Bool) where
  toFun σ u := !(σ u)
  invFun σ u := !(σ u)
  left_inv σ := by ext u; simp
  right_inv σ := by ext u; simp

omit [Fintype V] in
@[simp] lemma fieldAt_zero (v : V) : fieldAt v 0 = 0 := by
  ext u
  simp [fieldAt]

end

end BufferedIsing.DSS

end OAI


