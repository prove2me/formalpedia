-- Prove2me | Definitions.Def_IncompleteProc_English_Model
-- name    : IncompleteProc_English_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:06:00.826053+00:00
-- url     : https://prove2.me/theorems/645f5656-3d1f-4ed7-b40f-f130238b8698
-- title:
--   §2–§3, App. A.1, pp. 5–7, 13–16 — two-period procurement: cost shock k, virtual costs Ψ1, Ψ2, thresholds c⋆1, c⋆2, direct mechanisms, IC, IR, buyer surplus, Prop. 1 mechanism
-- statement:
--   The model of Gretschko and Pollrich's two-period procurement problem, together with the complete-contract benchmark.
--
--   **Environment.** A buyer purchases from $n \ge 1$ suppliers in two periods. She values each unit at $R > 0$; period 1 has quantity $1$ and period 2 has relative quantity $Q > 0$. Each supplier $i$ privately knows a first-period cost $c^i$; the costs are independent with density $f$ on $[\underline c, \bar c]$, $\underline c < \bar c$, where $f$ is measurable, integrates to $1$ and satisfies $f \ge \delta > 0$ on $[\underline c, \bar c]$. The distribution function is $F(c) = \int_{\underline c}^{c} f(s)\,ds$, and the law of the cost profile $C = (c^1, \dots, c^n)$ is the product density $\prod_i f(c^i)$ on the cube $[\underline c, \bar c]^n$. At the start of period 2 a publicly observed state $\omega \in \Omega$ is drawn from a probability measure $G$, and a supplier with first-period cost $c$ has second-period cost $k(c, \omega)$. For every $\omega$, $k(\cdot, \omega)$ is strictly increasing on $[\underline c, \bar c]$ with derivative $k_c(\cdot,\omega)$ satisfying $0 \le k_c \le K$. Write
--   $$H(c) = (1 - F(c))^{n-1}.$$
--
--   **Virtual costs and Assumption 1.** The first- and second-period virtual costs are
--   $$\Psi_1(c) = c + \frac{F(c)}{f(c)}, \qquad \Psi_2(c, \omega) = k(c, \omega) + \frac{F(c)}{f(c)}\, k_c(c, \omega).$$
--   Assumption 1 (maintained throughout the paper) requires $\Psi_1$ and every $\Psi_2(\cdot, \omega)$ to be non-decreasing on $[\underline c, \bar c]$.
--
--   **Thresholds.** The period-2 threshold $c^\star_2(\omega)$ is where $\Psi_2(\cdot, \omega)$ crosses $R$ (equation (2)), and the period-1 threshold $c^\star_1$ is where $\Psi_1$ crosses $R + \int_\Omega Q \max\{0, R - \Psi_2(\cdot, \omega)\}\, dG(\omega)$ (equation (1)):
--   $$c^\star_2(\omega) = \sup\big(\{\underline c\} \cup \{c \in [\underline c, \bar c] : \Psi_2(c, \omega) \le R\}\big),$$
--   $$c^\star_1 = \sup\Big(\{\underline c\} \cup \Big\{c \in [\underline c, \bar c] : \Psi_1(c) \le R + \int_\Omega Q \max\{0, R - \Psi_2(c, \omega)\}\, dG(\omega)\Big\}\Big).$$
--   The continuation set is $\Omega(c) = A(c) = \{\omega : k(c, \omega) \le k(c^\star_2(\omega), \omega)\}$. Two further functions of $c$ are $\Phi(c) = \int_\Omega Q \max\{0, k(c^\star_2(\omega), \omega) - k(c, \omega)\}\, dG(\omega)$ and $\varphi(c) = -\int_{\Omega(c)} Q\, k_c(c, \omega)\, dG(\omega)$.
--
--   **Direct mechanisms.** A direct mechanism assigns to each reported profile $C$ a probability $x^i_1(C)$ that supplier $i$ supplies in period 1, a probability $x^i_2(C, \omega)$ that he supplies in period 2 in state $\omega$, and a transfer $t^i(C)$. It is admissible when, on the cube, $x_1$ is a lottery ($x^i_1 \ge 0$, $\sum_i x^i_1 \le 1$), $x^i_2 \ge 0$ and $\sum_i x^i_2(C, \omega) \le \sum_i x^i_1(C)$ (the buyer buys in period 2 only if she bought in period 1), $x_1$ and $x_2$ are measurable and each $t^i$ is integrable. With $X^i_1(c)$, $X^i_2(c, \omega)$, $T^i(c)$ the expectations of $x^i_1, x^i_2, t^i$ when $i$ reports $c$ and the others report truthfully, supplier $i$'s profit from true cost $c$ and report $c'$ is
--   $$U^i(c, c') = T^i(c') - X^i_1(c')\, c - \int_\Omega Q\, k(c, \omega)\, X^i_2(c', \omega)\, dG(\omega).$$
--   The mechanism is incentive compatible (IC) if $U^i(c, c') \le U^i(c, c)$ for all $i$ and $c, c' \in [\underline c, \bar c]$, and individually rational (IR) if $U^i(c, c) \ge 0$ for all of them. Its buyer surplus is
--   $$\mathbb E\Big[\sum_{i=1}^n \Big(R\, x^i_1(C) + \int_\Omega Q R\, x^i_2(C, \omega)\, dG(\omega) - t^i(C)\Big)\Big].$$
--
--   **The mechanism of Proposition 1.** Supplier $i$ supplies in period 1 iff $c^i$ is the lowest cost and $c^i \le c^\star_1$, and in period 2 in state $\omega$ iff, in addition, $k(c^i, \omega) \le k(c^\star_2(\omega), \omega)$. Ties go to the lowest index. He receives $t^i(C) = T(c^i)$, where
--   $$T(c) = H(c)\Big(c + \int_{A(c)} Q k(c, \omega)\, dG\Big) + \int_c^{c^\star_1} H(s)\Big(1 + Q \int_{A(s)} k_c(s, \omega)\, dG\Big) ds \quad (c \le c^\star_1), \qquad T(c) = 0 \quad (c > c^\star_1).$$
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Several hypotheses and conventions differ from the page.
--   1. Added hypotheses: $n \ge 1$; measurability of $k(c, \cdot)$ and $k_c(c, \cdot)$ (the integrals against $G$ need it); and uniform boundedness of $k$ on $[\underline c, \bar c] \times \Omega$, which the proof of Lemma 1 (p. 14) asserts. The derivative is taken within $[\underline c, \bar c]$.
--   2. Thresholds: the page defines $c^\star_1$ and $c^\star_2(\omega)$ as the unique roots of (1) and (2), and as $\bar c$ when there is none. Here they are crossing points: they equal a root when there is one, $\bar c$ when the left side stays below the right, and $\underline c$ when it stays above. The page's "$\bar c$ otherwise" would make the buyer buy at a loss in the second case.
--   3. $A(c)$: the page writes $\{\omega : R - \Psi_2(c, \omega) \ge 0\}$ and identifies it with $\Omega(c)$ (footnote 16). Without continuity of $\Psi_2$ the two sets can differ at the crossing point, so $A(c)$ is taken to be the production set $\Omega(c)$, which keeps $T$ consistent with the allocation.
--   4. $x_2$ is read unconditionally: it is the probability of supplying in period 2, constrained by $\sum_i x^i_2 \le \sum_i x^i_1$. Where the page multiplies $X^i_2$ by $X^i_1$, the formulas are rewritten accordingly.
--   5. Under this reading, (4) gets the conjunct $c^i \le c^\star_1$, so that period-2 supply requires period-1 supply. It also gets $\underline c \le c^i$, which only matters outside the cost range.
-- source:
--   Gretschko & Pollrich, Incomplete Contracts in Dynamic Procurement, ZEW Discussion Paper No. 19-040 (Sept. 2019; SSRN 3466701), pp. 5–7 (PDF 6–8), §2 Model, Assumption 1, §3, eqs. (1)–(4); p. 13 (PDF 14), App. A.1 (Tⁱ, Xⁱ₁, Xⁱ₂, Uⁱ, IC, IR); pp. 14–15 (PDF 15–16), A(c), H(c), T(c); p. 16 (PDF 17), Ω(c), Φ, φ (8)

import Mathlib

namespace IncompleteProc.English

open MeasureTheory

/-- The primitive data of Gretschko–Pollrich's two-period procurement model (§2, pp. 5–6):
`n` suppliers; relative second-period quantity `Q = Q₂/Q₁` (with `Q₁ = 1`); the buyer's per-unit
value `R`; the support `[clo, chi]` (`[c̲, c̄]`) of first-period costs; the cost density `f`; the
distribution `G` of the state of the world `ω ∈ Ω`; the second-period cost function `k(c, ω)`;
its derivative `kc(c, ω)` in `c`; and the bound `K` on that derivative. -/
structure Env (Ω : Type*) [MeasurableSpace Ω] where
  n : ℕ
  Q : ℝ
  R : ℝ
  clo : ℝ
  chi : ℝ
  f : ℝ → ℝ
  G : Measure Ω
  k : ℝ → Ω → ℝ
  kc : ℝ → Ω → ℝ
  K : ℝ

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The distribution function `F(c) = ∫_{c̲}^{c} f`. -/
noncomputable def Env.F (E : Env Ω) (c : ℝ) : ℝ := ∫ s in E.clo..c, E.f s

/-- `H(c) = (1 − F(c))^{n−1}` (p. 15): the probability that the `n − 1` other suppliers all have
costs at least `c`. (`n ≥ 1` is part of `Standing`, so the natural subtraction is exact.) -/
noncomputable def Env.H (E : Env Ω) (c : ℝ) : ℝ := (1 - E.F c) ^ (E.n - 1)

/-- The first-period virtual cost `Ψ₁(c) = c + F(c)/f(c)` (Assumption 1 (i), p. 6). -/
noncomputable def Env.Psi1 (E : Env Ω) (c : ℝ) : ℝ := c + E.F c / E.f c

/-- The second-period virtual cost `Ψ₂(c, ω) = k(c, ω) + (F(c)/f(c)) k_c(c, ω)`
(Assumption 1 (ii), p. 6). -/
noncomputable def Env.Psi2 (E : Env Ω) (c : ℝ) (ω : Ω) : ℝ :=
  E.k c ω + E.F c / E.f c * E.kc c ω

/-- The cost cube `[c̲, c̄]^n`. -/
def Env.cube (E : Env Ω) : Set (Fin E.n → ℝ) := Set.univ.pi fun _ => Set.Icc E.clo E.chi

/-- The law of the cost profile `(c¹, …, cⁿ)`: i.i.d. costs with density `f` on `[c̲, c̄]`, i.e. the
measure with density `∏ᵢ f(cⁱ)` on the cube `[c̲, c̄]^n`. -/
noncomputable def Env.profileLaw (E : Env Ω) : Measure (Fin E.n → ℝ) :=
  (volume.restrict E.cube).withDensity fun C => ∏ i, ENNReal.ofReal (E.f (C i))

/-- The standing assumptions of §2 (pp. 5–6):
`n ≥ 1` (added: "n suppliers"); `Q > 0`, `R > 0`; `c̲ < c̄`; `f` measurable and integrable on
`[c̲, c̄]` with total mass `1` and bounded away from `0` there; `G` a probability measure; for every
`ω`, `k(·, ω)` strictly increasing on `[c̲, c̄]` with derivative `kc(·, ω)` (within `[c̲, c̄]`) and
`0 ≤ kc ≤ K`; `k(c, ·)` and `kc(c, ·)` measurable (added: the integrals against `G` need it); `k`
bounded on `[c̲, c̄] × Ω` (added: "because k(c, ω) is uniformly bounded", proof of Lemma 1, p. 14). -/
def Env.Standing (E : Env Ω) : Prop :=
  1 ≤ E.n ∧ 0 < E.Q ∧ 0 < E.R ∧ E.clo < E.chi ∧
  Measurable E.f ∧ IntegrableOn E.f (Set.Icc E.clo E.chi) ∧ ∫ c in E.clo..E.chi, E.f c = 1 ∧
  (∃ δ > 0, ∀ c ∈ Set.Icc E.clo E.chi, δ ≤ E.f c) ∧
  IsProbabilityMeasure E.G ∧
  (∀ ω, StrictMonoOn (E.k · ω) (Set.Icc E.clo E.chi)) ∧
  (∀ ω, ∀ c ∈ Set.Icc E.clo E.chi,
    HasDerivWithinAt (E.k · ω) (E.kc c ω) (Set.Icc E.clo E.chi) c) ∧
  (∀ ω, ∀ c ∈ Set.Icc E.clo E.chi, 0 ≤ E.kc c ω ∧ E.kc c ω ≤ E.K) ∧
  (∀ c, Measurable (E.k c)) ∧ (∀ c, Measurable (E.kc c)) ∧
  (∃ M : ℝ, ∀ c ∈ Set.Icc E.clo E.chi, ∀ ω, |E.k c ω| ≤ M)

/-- Assumption 1 (p. 6), maintained throughout the paper: `Ψ₁` is non-decreasing on `[c̲, c̄]`, and
`Ψ₂(·, ω)` is non-decreasing on `[c̲, c̄]` for every `ω`. -/
def Env.Assumption1 (E : Env Ω) : Prop :=
  MonotoneOn E.Psi1 (Set.Icc E.clo E.chi) ∧
    ∀ ω, MonotoneOn (E.Psi2 · ω) (Set.Icc E.clo E.chi)

/-- The second-period threshold `c⋆₂(ω)` of (2), p. 7, as the crossing point of `Ψ₂(·, ω)` and `R`:
the supremum of `{c ∈ [c̲, c̄] | Ψ₂(c, ω) ≤ R}` together with `c̲`. It is the solution of (2) when one
exists, `c̄` when `Ψ₂(·, ω) < R` throughout, and `c̲` when `Ψ₂(·, ω) > R` throughout. -/
noncomputable def Env.cStar2 (E : Env Ω) (ω : Ω) : ℝ :=
  sSup (insert E.clo {c ∈ Set.Icc E.clo E.chi | E.Psi2 c ω ≤ E.R})

/-- The first-period threshold `c⋆₁` of (1), p. 7, as the crossing point of `Ψ₁` and
`R + ∫ Q max{0, R − Ψ₂(·, ω)} dG`: the supremum of the set of `c ∈ [c̲, c̄]` with
`Ψ₁(c) ≤ R + ∫_Ω Q max{0, R − Ψ₂(c, ω)} dG(ω)`, together with `c̲`. -/
noncomputable def Env.cStar1 (E : Env Ω) : ℝ :=
  sSup (insert E.clo {c ∈ Set.Icc E.clo E.chi |
    E.Psi1 c ≤ E.R + ∫ ω, E.Q * max 0 (E.R - E.Psi2 c ω) ∂E.G})

/-- The continuation set `Ω(c) = A(c) = {ω | k(c, ω) ≤ k(c⋆₂(ω), ω)}` (p. 16 and footnote 16; the
set of states in which period-two production continues when the winner's cost is `c`, p. 14). -/
def Env.contSet (E : Env Ω) (c : ℝ) : Set Ω := {ω | E.k c ω ≤ E.k (E.cStar2 ω) ω}

/-- `Φ(c) = ∫_Ω Q max{0, k(c⋆₂(ω), ω) − k(c, ω)} dG(ω)` (p. 16). -/
noncomputable def Env.Phi (E : Env Ω) (c : ℝ) : ℝ :=
  ∫ ω, E.Q * max 0 (E.k (E.cStar2 ω) ω - E.k c ω) ∂E.G

/-- `φ(c) = −∫_{Ω(c)} Q k_c(c, ω) dG(ω)` ((8), p. 16). -/
noncomputable def Env.phi (E : Env Ω) (c : ℝ) : ℝ :=
  -∫ ω in E.contSet c, E.Q * E.kc c ω ∂E.G

/-- A direct mechanism (§3, p. 6) for `n` suppliers: the probability `x1 C i` that supplier `i`
supplies in period 1, the probability `x2 C ω i` that supplier `i` supplies in period 2 in state
`ω` (unconditional), and the transfer `t C i` to supplier `i`, all as functions of the reported
cost profile `C`. Transfers do not depend on `ω` (footnote 7). -/
structure Mech (n : ℕ) (Ω : Type*) where
  x1 : (Fin n → ℝ) → Fin n → ℝ
  x2 : (Fin n → ℝ) → Ω → Fin n → ℝ
  t : (Fin n → ℝ) → Fin n → ℝ

/-- Admissibility of a direct mechanism: on the cube, `x1` is a lottery over `{0, 1, …, n}`
(non-negative, total at most `1`), and `x2(·, ω)` is non-negative with total at most the total of
`x1` (the buyer can only purchase in period 2 if she purchased in period 1, p. 5); `x1` and `x2`
(jointly in the profile and the state) are measurable and every transfer is integrable. -/
def Mech.Admissible (E : Env Ω) (M : Mech E.n Ω) : Prop :=
  (∀ C ∈ E.cube, (∀ i, 0 ≤ M.x1 C i) ∧ ∑ i, M.x1 C i ≤ 1) ∧
  (∀ C ∈ E.cube, ∀ ω, (∀ i, 0 ≤ M.x2 C ω i) ∧ ∑ i, M.x2 C ω i ≤ ∑ i, M.x1 C i) ∧
  (∀ i, Measurable fun C => M.x1 C i) ∧
  (∀ i, Measurable fun p : (Fin E.n → ℝ) × Ω => M.x2 p.1 p.2 i) ∧
  (∀ i, Integrable (fun C => M.t C i) E.profileLaw)

/-- The interim first-period allocation `X¹ᵢ(c) = E[x¹ᵢ(c, C⁻ⁱ)]` (p. 13). -/
noncomputable def Mech.X1 (E : Env Ω) (M : Mech E.n Ω) (i : Fin E.n) (c : ℝ) : ℝ :=
  ∫ C, M.x1 (Function.update C i c) i ∂E.profileLaw

/-- The interim second-period allocation `X²ᵢ(c, ω) = E[x²ᵢ(c, C⁻ⁱ, ω)]` (p. 13). -/
noncomputable def Mech.X2 (E : Env Ω) (M : Mech E.n Ω) (i : Fin E.n) (c : ℝ) (ω : Ω) : ℝ :=
  ∫ C, M.x2 (Function.update C i c) ω i ∂E.profileLaw

/-- The interim transfer `Tⁱ(c) = E[tⁱ(c, C⁻ⁱ)]` (p. 13). -/
noncomputable def Mech.T (E : Env Ω) (M : Mech E.n Ω) (i : Fin E.n) (c : ℝ) : ℝ :=
  ∫ C, M.t (Function.update C i c) i ∂E.profileLaw

/-- Supplier `i`'s expected profit `Uⁱ(c, c′)` when his cost is `c` and he reports `c′` (p. 13), with
`x2` read unconditionally: `Tⁱ(c′) − X¹ᵢ(c′) c − ∫_Ω Q k(c, ω) X²ᵢ(c′, ω) dG(ω)`. -/
noncomputable def Mech.U (E : Env Ω) (M : Mech E.n Ω) (i : Fin E.n) (c c' : ℝ) : ℝ :=
  M.T E i c' - M.X1 E i c' * c - ∫ ω, E.Q * E.k c ω * M.X2 E i c' ω ∂E.G

/-- Incentive compatibility (p. 13): `Uⁱ(c) ≥ Uⁱ(c, c′)` for all `i` and `c, c′ ∈ [c̲, c̄]`. -/
def Mech.IsIC (E : Env Ω) (M : Mech E.n Ω) : Prop :=
  ∀ i, ∀ c ∈ Set.Icc E.clo E.chi, ∀ c' ∈ Set.Icc E.clo E.chi, M.U E i c c' ≤ M.U E i c c

/-- Individual rationality (p. 13): `Uⁱ(c) ≥ 0` for all `i` and `c ∈ [c̲, c̄]`. -/
def Mech.IsIR (E : Env Ω) (M : Mech E.n Ω) : Prop :=
  ∀ i, ∀ c ∈ Set.Icc E.clo E.chi, 0 ≤ M.U E i c c

/-- The buyer surplus of a direct mechanism (p. 14):
`E[∑ᵢ (R x¹ᵢ(C) + ∫_Ω Q R x²ᵢ(C, ω) dG(ω) − tⁱ(C))]`. -/
noncomputable def Mech.buyerSurplus (E : Env Ω) (M : Mech E.n Ω) : ℝ :=
  ∫ C, ∑ i, (E.R * M.x1 C i + ∫ ω, E.Q * E.R * M.x2 C ω i ∂E.G - M.t C i) ∂E.profileLaw

/-- The buyer surpluses attainable with complete contracts: those of admissible, incentive
compatible and individually rational direct mechanisms. -/
def Env.feasibleSurplus (E : Env Ω) : Set ℝ :=
  {s | ∃ M : Mech E.n Ω, M.Admissible E ∧ M.IsIC E ∧ M.IsIR E ∧ s = M.buyerSurplus E}

/-- Supplier `i` has the lowest cost in `C`, ties broken in favour of the lowest index. -/
def isLowest {n : ℕ} (C : Fin n → ℝ) (i : Fin n) : Prop :=
  (∀ j, j < i → C i < C j) ∧ (∀ j, i < j → C i ≤ C j)

/-- The transfer rule `T(c)` of the proof of Proposition 1 (p. 15), with `A(c) = Ω(c)`:
for `c ≤ c⋆₁`,
`T(c) = H(c)(c + ∫_{A(c)} Q k(c, ω) dG) + ∫_c^{c⋆₁} H(s)(1 + Q ∫_{A(s)} k_c(s, ω) dG) ds`,
and `T(c) = 0` for `c > c⋆₁`. -/
noncomputable def Env.optTransfer (E : Env Ω) (c : ℝ) : ℝ :=
  if c ≤ E.cStar1 then
    E.H c * (c + ∫ ω in E.contSet c, E.Q * E.k c ω ∂E.G) +
      ∫ s in c..E.cStar1, E.H s * (1 + E.Q * ∫ ω in E.contSet s, E.kc s ω ∂E.G)
  else 0

open Classical in
/-- The direct mechanism of Proposition 1 (p. 7) with the transfer rule of p. 15:
(3) supplier `i` supplies in period 1 iff he has the lowest cost and `cⁱ ≤ c⋆₁`;
(4) he supplies in period 2 in state `ω` iff, in addition, `k(cⁱ, ω) ≤ k(c⋆₂(ω), ω)`;
`tⁱ(C) = T(cⁱ)`. Ties go to the lowest index. In (4) the conjunct `cⁱ ≤ c⋆₁` is added (period-2
purchase requires a period-1 purchase), and `c̲ ≤ cⁱ` restricts (4) to the cost range. -/
noncomputable def Env.optMech (E : Env Ω) : Mech E.n Ω where
  x1 C i := if C i ≤ E.cStar1 ∧ isLowest C i then 1 else 0
  x2 C ω i := if C i ≤ E.cStar1 ∧ isLowest C i ∧ E.clo ≤ C i ∧
      E.k (C i) ω ≤ E.k (E.cStar2 ω) ω then 1 else 0
  t C i := E.optTransfer (C i)

end IncompleteProc.English


