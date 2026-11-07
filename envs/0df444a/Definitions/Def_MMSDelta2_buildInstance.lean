-- Prove2me | Definitions.Def_MMSDelta2_buildInstance
-- name    : MMSDelta2_buildInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:00:59.875782+00:00
-- url     : https://prove2.me/theorems/bba97879-45f1-4640-8e98-d071e5288843
-- title:
--   The five-agent goods instance of the §7 reduction
-- statement:
--   Given a 4-PARTITION instance, the reduction builds an additive goods instance with five agents: a puzzle-solving agent $p$, a lex-opt indicator $a^*$, two row-forcing agents $q_1,q_2$ and an anchor agent $f$. The goods are the **core goods** $g_{r,s}$, one for each $(r,s)\in A^+$ (19 of them), and the **assignment goods** $h_{i,j}$, $(i,j)\in[m]\times[\ell]$. Core values are $v_z(g_{r,s})=\Gamma A_{r,s}+\delta_z(r,s)$, where all perturbations not listed are $0$:
--
--   1. $p$: $v_p(h_{i,j})=c_{i,j}-\varepsilon_{i,j}$; $\delta_p(r,5)=-B$ for $r\in[4]$, $\delta_p(5,5)=4B-V_P$;
--   2. $a^*$: $v_{a^*}(h_{i,j})=Kc_{i,j}-\omega_{i,j}$; with $\beta_1=F-KB$, $\beta_2=W_{sc}-K(C_{tot}-B)$, $\beta_3=\beta_4=\beta_5=F$, $\gamma_1=W_{sc}-K(C_{tot}-B)$, $\gamma_2=\gamma_3=\gamma_4=-U$: $\delta_{a^*}(r,5)=\gamma_r$ ($r\in[4]$), $\delta_{a^*}(5,s)=\beta_s$ ($s\in[4]$), $\delta_{a^*}(5,5)=\beta_5-\sum_{r=1}^4\gamma_r$;
--   3. $q_1,q_2$: $\delta_q(5,s)=-1$ ($s\in[4]$), $\delta_q(5,5)=4$, and value $0$ on every assignment good;
--   4. $f$: $\delta_f(r,5)=-1$ ($r\in[4]$), $\delta_f(5,5)=4$, and value $0$ on every assignment good.
--
--   The scale is $\Gamma=1+\max_z\big(\sum_{(r,s)\in A^+}|\delta_z(r,s)|+V_z\big)$ with $V_z=v_z(M_{asg})$, and $\tau=\Gamma\alpha$. The item also names the core goods $M_{core}$ and the core goods $R_r$ of row $r$ and $C_s$ of column $s$.
--
--   **Formalization Note** Agents are numbered $0=p$, $1=a^*$, $2=q_1$, $3=q_2$, $4=f$; rows and columns are 0-based. The goods are indexed by $\{0,\dots,\mathrm{numCore}+4\ell\cdot\ell-1\}$ with $\mathrm{numCore}=|A^+|$ ($=19$): good $k<\mathrm{numCore}$ is the core good at the $k$-th position of $A^+$ in the order $5r+s$, and good $\mathrm{numCore}+\ell i+j$ is $h_{i,j}$. All values are integers, returned as rationals.
-- source:
--   Gupta, Seetharaman, The Existence of Maximin Share Allocations is Δ₂ᴾ-complete, arXiv:2609.15841 (held version, sha256 a43b06b9…), §7.1.1–§7.1.3, pp.28–32 (PDF pp.30–34)

import Mathlib
import Definitions.Def_MMSDelta2_KPW
import Definitions.Def_MMSDelta2_Parameters

namespace MMSDelta2

/-!
# The five-agent goods instance of the §7 reduction

S. Gupta, S. Seetharaman, *The Existence of Maximin Share Allocations is Δ₂ᴾ-complete*,
arXiv:2609.15841 (held version, sha256 a43b06b9…), §7.1.1–§7.1.3, pp.28–32 (PDF pp.30–34).
Five agents: the puzzle-solving agent `p`, the lex-opt indicator `a*`, two row-forcing agents
`q_1, q_2` and the anchor agent `f`. Goods: one core good `g_{r,s}` per `(r,s) ∈ A⁺` and one
assignment good `h_{i,j}` per `(i,j) ∈ [m] × [ℓ]`. Values `v_z(g_{r,s}) = ΓA_{r,s} + δ_z(r,s)` with
the perturbations
* `p`: `v_p(h_{i,j}) = c_{i,j} − ε_{i,j}`, `δ_p(r,5) = −B` (`r ∈ [4]`), `δ_p(5,5) = 4B − V_P`;
* `a*`: `v_{a*}(h_{i,j}) = K c_{i,j} − ω_{i,j}`; `β_1 = F − KB`, `β_2 = W_sc − K(C_tot − B)`,
  `β_3 = β_4 = β_5 = F`, `γ_1 = W_sc − K(C_tot − B)`, `γ_2 = γ_3 = γ_4 = −U`; `δ(r,5) = γ_r`
  (`r ∈ [4]`), `δ(5,s) = β_s` (`s ∈ [4]`), `δ(5,5) = β_5 − Σ_{r=1}^4 γ_r`;
* `q_1, q_2`: `δ(5,s) = −1` (`s ∈ [4]`), `δ(5,5) = 4`, value `0` on assignment goods;
* `f`: `δ(r,5) = −1` (`r ∈ [4]`), `δ(5,5) = 4`, value `0` on assignment goods;
all other perturbations zero; `Γ = 1 + max_z (Σ_{(r,s)∈A⁺} |δ_z(r,s)| + V_z)`, `V_z = v_z(M_asg)`,
`τ = Γα`.

**Formalization Note.**
* Agents are `Fin 5`: `0 = p`, `1 = a*`, `2 = q_1`, `3 = q_2`, `4 = f`. Rows and columns are 0-based
  (`4` is the paper's `5`).
* Goods are `Fin (numCore + 4ℓ·ℓ)`: index `k < numCore` is the core good at the `k`-th position of
  `A⁺` in the order `5r + s`; index `numCore + (ℓi + j)` is `h_{i,j}` (0-based `i, j`).
  `numCore = |A⁺|`.
* `gamma` has a fifth entry `0`, which is never used.
* All values are integers; `buildInstance` returns them as rationals.
-/

/-- The positions of `A⁺` as elements of `Fin 25` (position `(r,s)` is `5r + s`). -/
def corePosSet : Finset (Fin (5 * 5)) := kpwAplus.map finProdFinEquiv.toEmbedding

/-- The number of core goods, `|A⁺|`. -/
def numCore : ℕ := corePosSet.card

/-- The position `(r, s)` of the `k`-th core good. -/
def corePos (k : Fin numCore) : Fin 5 × Fin 5 :=
  finProdFinEquiv.symm (corePosSet.orderIsoOfFin rfl k).1

namespace FourPartInstance

variable (I : FourPartInstance)

/-- The column offsets `β_1, …, β_5` of the lex-opt indicator. -/
def beta : Fin 5 → ℤ :=
  ![I.F - I.K * I.B, (I.Wsc : ℤ) - I.K * ((I.Ctot : ℤ) - I.B), I.F, I.F, I.F]

/-- The row offsets `γ_1, …, γ_4` of the lex-opt indicator (fifth entry unused). -/
def gamma : Fin 5 → ℤ :=
  ![(I.Wsc : ℤ) - I.K * ((I.Ctot : ℤ) - I.B), -I.U, -I.U, -I.U, 0]

/-- The perturbation `δ_z(r, s)` of agent `z` at core position `(r, s)`. -/
def delta (z r s : Fin 5) : ℤ :=
  if z = 0 then
    (if r = 4 ∧ s = 4 then 4 * (I.B : ℤ) - I.VP else if s = 4 then -(I.B : ℤ) else 0)
  else if z = 1 then
    (if r = 4 ∧ s = 4 then I.beta 4 - ∑ k : Fin 4, I.gamma k.castSucc
      else if r = 4 then I.beta s else if s = 4 then I.gamma r else 0)
  else if z = 4 then
    (if r = 4 ∧ s = 4 then 4 else if s = 4 then -1 else 0)
  else
    (if r = 4 ∧ s = 4 then 4 else if r = 4 then -1 else 0)

/-- The value `v_z(h_{i,j})` of agent `z` for the assignment good `h_{i,j}`. -/
def asgVal (z : Fin 5) (i : Fin (4 * I.q)) (j : Fin I.q) : ℤ :=
  if z = 0 then (I.cons i j : ℤ) - I.pen i j
  else if z = 1 then I.K * I.cons i j - I.omega i j
  else 0

/-- `V_z = v_z(M_asg)`. -/
def V (z : Fin 5) : ℤ := ∑ i, ∑ j, I.asgVal z i j

/-- The scaling factor `Γ = 1 + max_z (Σ_{(r,s)∈A⁺} |δ_z(r,s)| + V_z)`. -/
def Gam : ℤ :=
  1 + Finset.univ.sup' Finset.univ_nonempty
    (fun z : Fin 5 => ∑ p ∈ kpwAplus, |I.delta z p.1 p.2| + I.V z)

/-- `τ = Γα`. -/
def tau : ℤ := I.Gam * kpwAlpha

/-- The value `v_z(g_{r,s}) = ΓA_{r,s} + δ_z(r,s)` of the core good at `(r, s)`. -/
def coreVal (z r s : Fin 5) : ℤ := I.Gam * kpwA r s + I.delta z r s

/-- The kind of good `g`: a core good (by its index in `A⁺`) or an assignment good `h_{i,j}`. -/
def goodKind (g : Fin (numCore + 4 * I.q * I.q)) : Fin numCore ⊕ (Fin (4 * I.q) × Fin I.q) :=
  Sum.map id finProdFinEquiv.symm (finSumFinEquiv.symm g)

/-- The constructed five-agent additive goods instance. -/
def buildInstance : Fin 5 → Fin (numCore + 4 * I.q * I.q) → ℚ := fun z g =>
  match I.goodKind g with
  | .inl k => (I.coreVal z (corePos k).1 (corePos k).2 : ℚ)
  | .inr p => (I.asgVal z p.1 p.2 : ℚ)

/-- The core position of good `g`, if it is a core good. -/
def corePosOf (g : Fin (numCore + 4 * I.q * I.q)) : Option (Fin 5 × Fin 5) :=
  match I.goodKind g with
  | .inl k => some (corePos k)
  | .inr _ => none

/-- `M_core`, the core goods. -/
def coreGoods : Finset (Fin (numCore + 4 * I.q * I.q)) :=
  Finset.univ.filter fun g => (I.corePosOf g).isSome

/-- `R_r`, the core goods of row `r`. -/
def rowGoods (r : Fin 5) : Finset (Fin (numCore + 4 * I.q * I.q)) :=
  Finset.univ.filter fun g => (I.corePosOf g).map Prod.fst = some r

/-- `C_s`, the core goods of column `s`. -/
def colGoods (s : Fin 5) : Finset (Fin (numCore + 4 * I.q * I.q)) :=
  Finset.univ.filter fun g => (I.corePosOf g).map Prod.snd = some s

end FourPartInstance

end MMSDelta2


