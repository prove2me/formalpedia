-- Prove2me | Definitions.Def_ArrowDebreu_ThmII_AssumptionsII
-- name    : ArrowDebreu_ThmII_AssumptionsII
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T22:14:53.015006+00:00
-- url     : https://prove2.me/theorems/ef9dba8f-2dd9-40b5-a67d-dfcb5f8ead30
-- title:
--   Assumptions I–III, IV′, V–VII; desired commodities $\mathcal D$ and productive labor $\mathcal P$
-- statement:
--   The hypotheses of Theorem II, each as a separate predicate on an economy.
--
--   - **I.a** Each $Y_j$ is closed, convex and contains $0$. **I.b** $Y\cap\Omega=\{0\}$. **I.c** $Y\cap(-Y)=\{0\}$.
--   - **II** Each $X_i$ is closed, convex and bounded from below: $\xi_i\leqq x_i$ for some $\xi_i$ and all $x_i\in X_i$.
--   - **III.a** $u_i$ is continuous on $X_i$. **III.b** For every $x_i\in X_i$ there is $x_i'\in X_i$ with $u_i(x_i')>u_i(x_i)$. **III.c** If $x_i,x_i'\in X_i$, $u_i(x_i)>u_i(x_i')$ and $0<t<1$, then $u_i(tx_i+(1-t)x_i')>u_i(x_i')$.
--   - **IV.b** $\alpha_{ij}\ge0$ and $\sum_i\alpha_{ij}=1$ for every $j$.
--
--   Let $\delta^h$ be the $h$-th unit vector. A commodity $h$ is **always desired** ($h\in\mathcal D$) if for every consumer $i$ and every $x_i\in X_i$ there is $\lambda>0$ with $x_i+\lambda\delta^h\in X_i$ and $u_i(x_i+\lambda\delta^h)>u_i(x_i)$. A commodity $h$ is a **type of productive labor** ($h\in\mathcal P$) if for every $y\in Y$: (a) $y_h\le0$, and (b) there is $y'\in Y$ with $y'_{h'}\ge y_{h'}$ for all $h'\ne h$ and $y'_{h''}>y_{h''}$ for at least one $h''\in\mathcal D$.
--
--   - **IV′.a** For every $i$ there is $x_i\in X_i$ with $x_i\leqq\zeta_i$ and $x_{hi}<\zeta_{hi}$ for at least one $h\in\mathcal P$.
--   - **V** There are $x\in X=\sum_iX_i$ and $y\in Y$ with
--   $$x_h<y_h+\zeta_h\quad\text{for every commodity }h.$$
--   - **VI** $\mathcal D\neq\emptyset$. **VII** $\mathcal P\neq\emptyset$.
--
--   Theorem II replaces Theorem I's Assumption IV.a (every consumer can supply a positive amount of every good) by IV′.a: every consumer can supply some productive labor. The bundle without V is also provided, because the intermediate steps of the proof do not use V.
--
--   **Formalization Note** Clause (b) of $\mathcal P$ is stated as printed: it does not require $h''\ne h$. $\mathcal D$ and $\mathcal P$ are finite sets of commodity indices computed from the economy, not parameters. The paper's strict vector inequality $x<y+\zeta$ is componentwise.
--
--   The file also defines the aggregate consumption set $X=\sum_{i=1}^m X_i=\{\sum_i x_i : x_i\in X_i\}$ (§4.2, p. 280, PDF p. 17), used in Assumption V, and the total initial holdings $\zeta=\sum_{i=1}^m\zeta_i$ (§1.4.1, p. 271, PDF p. 8).
-- source:
--   Arrow & Debreu, Econometrica 22 (1954), https://doi.org/10.2307/1907353, pp. 267–270 (PDF pp. 4–7) Assumptions I.a–I.c, II, III.a–III.c, IV.b; p. 280 (PDF p. 17) §4.1 IV′.a, §4.2 V, §4.3 Definition of 𝒟 and VI, §4.4 Definition of 𝒫 and VII; §4.2 (X = Σ X_i) and §1.4.1 (ζ = Σ ζ_i), p. 271 (PDF p. 8)

import Mathlib
import Definitions.Def_ArrowDebreu_Shared_Economy
open ArrowDebreu.Shared

namespace ArrowDebreu.ThmII

/-- The aggregate consumption set `X = Σ_{i=1}^m X_i` (§4.2, p. 280, PDF p. 17), the set sum of
§1.2.1: the vectors `Σ_i x_i` with `x_i ∈ X_i` for every `i`. With `m = 0` it is `{0}`. -/
def aggCons {l m n : ℕ} (E : Economy l m n) : Set (Fin l → ℝ) :=
  {v | ∃ x : Fin m → Fin l → ℝ, (∀ i, x i ∈ E.X i) ∧ v = ∑ i, x i}

/-- The total initial holdings `ζ = Σ_{i=1}^m ζ_i` (§1.4.1, p. 271, PDF p. 8). -/
def totalEndowment {l m n : ℕ} (E : Economy l m n) : Fin l → ℝ := ∑ i, E.ζ i

variable {l m n : ℕ}

/-- **Assumption I.a** (§1.2.2, p. 267, PDF p. 4): `Y_j` is a closed convex subset of `R^l`
containing `0` (`j = 1, ⋯, n`). -/
def AssumptionIa (E : Economy l m n) : Prop :=
  ∀ j, IsClosed (E.Y j) ∧ Convex ℝ (E.Y j) ∧ (0 : Fin l → ℝ) ∈ E.Y j

/-- **Assumption I.b** (§1.2.2, p. 267, PDF p. 4): `Y ∩ Ω = 0`, i.e. the aggregate production set
meets the nonnegative orthant exactly in `{0}` ("= 0" is equality with the set `{0}`). -/
def AssumptionIb (E : Economy l m n) : Prop :=
  aggProd E ∩ Ω l = {0}

/-- **Assumption I.c** (§1.2.2, p. 267, PDF p. 4): `Y ∩ (−Y) = 0`, equality with the set `{0}`. -/
def AssumptionIc (E : Economy l m n) : Prop :=
  aggProd E ∩ negSet (aggProd E) = {0}

/-- **Assumption II** (§1.3.0, p. 268, PDF p. 5): for every consumer `i`, `X_i` is a closed convex
subset of `R^l` which is bounded from below, i.e. there is a vector `ξ_i` with `ξ_i ≦ x_i` for all
`x_i ∈ X_i` (componentwise order). -/
def AssumptionII (E : Economy l m n) : Prop :=
  ∀ i, IsClosed (E.X i) ∧ Convex ℝ (E.X i) ∧ ∃ ξ : Fin l → ℝ, ∀ x ∈ E.X i, ξ ≤ x

/-- **Assumption III.a** (§1.3.1, p. 269, PDF p. 6): `u_i` is a continuous function on `X_i`, for
every consumer `i`. -/
def AssumptionIIIa (E : Economy l m n) : Prop :=
  ∀ i, ContinuousOn (E.u i) (E.X i)

/-- **Assumption III.b** (§1.3.1, p. 269, PDF p. 6): for any `x_i ∈ X_i` there is `x_i' ∈ X_i`
with `u_i(x_i') > u_i(x_i)` (no satiation), for every consumer `i`. -/
def AssumptionIIIb (E : Economy l m n) : Prop :=
  ∀ i, ∀ x ∈ E.X i, ∃ x' ∈ E.X i, E.u i x < E.u i x'

/-- **Assumption III.c** (§1.3.1, p. 269, PDF p. 6): if `u_i(x_i) > u_i(x_i')` and `0 < t < 1`,
then `u_i[t x_i + (1 − t) x_i'] > u_i(x_i')`, for every consumer `i` and all `x_i, x_i' ∈ X_i`. -/
def AssumptionIIIc (E : Economy l m n) : Prop :=
  ∀ i, ∀ x ∈ E.X i, ∀ x' ∈ E.X i, E.u i x' < E.u i x →
    ∀ t : ℝ, 0 < t → t < 1 → E.u i x' < E.u i (t • x + (1 - t) • x')

/-- **Assumption IV.b** (§1.3.2, p. 270, PDF p. 7): for all `i, j`, `α_{ij} ≧ 0`; for all `j`,
`Σ_{i=1}^m α_{ij} = 1`. -/
def AssumptionIVb (E : Economy l m n) : Prop :=
  (∀ i j, 0 ≤ E.α i j) ∧ ∀ j, ∑ i, E.α i j = 1

/-- `δ^h`, the positive unit vector of the `h`-th axis in `R^l` (§4.3, p. 280, PDF p. 17). -/
def unitVec (h : Fin l) : Fin l → ℝ := Pi.single h 1

/-- Commodity `h` is **always desired by every consumer** (Definition, §4.3, p. 280, PDF p. 17):
for every `i = 1, ⋯, m` and every `x_i ∈ X_i` there exists `λ > 0` such that `x_i + λδ^h ∈ X_i`
and `u_i(x_i + λδ^h) > u_i(x_i)`. (`λ` may depend on `i` and `x_i`.) -/
def IsDesired (E : Economy l m n) (h : Fin l) : Prop :=
  ∀ i, ∀ x ∈ E.X i, ∃ lam : ℝ, 0 < lam ∧ x + lam • unitVec h ∈ E.X i ∧
    E.u i x < E.u i (x + lam • unitVec h)

/-- The set `𝒟` of commodities which are always desired by every consumer (Definition, §4.3,
p. 280, PDF p. 17), as a finite set of commodity indices. -/
noncomputable def desired (E : Economy l m n) : Finset (Fin l) := by
  classical exact Finset.univ.filter (fun h => IsDesired E h)

theorem mem_desired (E : Economy l m n) (h : Fin l) : h ∈ desired E ↔ IsDesired E h := by
  classical
  unfold desired
  simp

/-- Commodity `h` is a **type of productive labor** (Definition, §4.4, p. 280, PDF p. 17): for
every `y ∈ Y` (the aggregate production set),
(a) `y_h ≦ 0`, and
(b) for some `y' ∈ Y` and all `h' ≠ h`, `y'_{h'} ≧ y_{h'}`, while for at least one `h'' ∈ 𝒟`,
`y'_{h''} > y_{h''}`.

**Formalization Note.** Clause (b) is stated as printed: the paper does not require `h'' ≠ h`, and
neither does this definition. -/
def IsProductive (E : Economy l m n) (h : Fin l) : Prop :=
  ∀ y ∈ aggProd E, y h ≤ 0 ∧
    ∃ y' ∈ aggProd E, (∀ h', h' ≠ h → y h' ≤ y' h') ∧ ∃ h'' ∈ desired E, y h'' < y' h''

/-- The set `𝒫` of types of productive labor (Definition, §4.4, p. 280, PDF p. 17), as a finite set
of commodity indices. Its number of elements is the paper's `π` (§5.0). -/
noncomputable def productive (E : Economy l m n) : Finset (Fin l) := by
  classical exact Finset.univ.filter (fun h => IsProductive E h)

theorem mem_productive (E : Economy l m n) (h : Fin l) : h ∈ productive E ↔ IsProductive E h := by
  classical
  unfold productive
  simp

/-- **Assumption IV′.a** (§4.1, p. 280, PDF p. 17): `ζ_i ∈ R^l`; for some `x_i ∈ X_i`, `x_i ≦ ζ_i`
and, for at least one `h ∈ 𝒫`, `x_{hi} < ζ_{hi}` — for every consumer `i`. The same `x_i` serves
both clauses. -/
def AssumptionIVa' (E : Economy l m n) : Prop :=
  ∀ i, ∃ x ∈ E.X i, x ≤ E.ζ i ∧ ∃ h ∈ productive E, x h < E.ζ i h

/-- **Assumption V** (§4.2, p. 280, PDF p. 17): there exist `x ∈ X = Σ_i X_i` and `y ∈ Y` such that
`x < y + ζ`.

**Formalization Note.** The paper's `x < y` means `x_h < y_h` for *every* component `h` (§1.2.1);
it is written componentwise, not with Lean's `<` on `Fin l → ℝ` (which means `≤` and `≠`). -/
def AssumptionV (E : Economy l m n) : Prop :=
  ∃ x ∈ aggCons E, ∃ y ∈ aggProd E, ∀ h, x h < y h + totalEndowment E h

/-- **Assumption VI** (§4.3, p. 280, PDF p. 17): the set `𝒟` is not empty. -/
def AssumptionVI (E : Economy l m n) : Prop :=
  (desired E).Nonempty

/-- **Assumption VII** (§4.4, p. 280, PDF p. 17): the set `𝒫` is not empty. -/
def AssumptionVII (E : Economy l m n) : Prop :=
  (productive E).Nonempty

/-- **Assumptions I–III, IV′, VI and VII** (§4, pp. 279–281, PDF pp. 16–18): the hypotheses of
Theorem II except Assumption V — I.a, I.b, I.c, II, III.a, III.b, III.c, IV′.a, IV.b, VI and VII,
each a separate field. The paper uses Assumption V only in §5.3.5 (p. 287); the intermediate
statements of §5 are stated under this weaker bundle. -/
structure AssumptionsIIexceptV (E : Economy l m n) : Prop where
  Ia : AssumptionIa E
  Ib : AssumptionIb E
  Ic : AssumptionIc E
  II : AssumptionII E
  IIIa : AssumptionIIIa E
  IIIb : AssumptionIIIb E
  IIIc : AssumptionIIIc E
  IVa' : AssumptionIVa' E
  IVb : AssumptionIVb E
  VI : AssumptionVI E
  VII : AssumptionVII E

/-- **Assumptions I–III, IV′, and V–VII** (§4, pp. 279–281, PDF pp. 16–18), the hypotheses of
Theorem II: I.a, I.b, I.c, II, III.a, III.b, III.c, IV′.a, IV.b, V, VI and VII — the bundle
`AssumptionsIIexceptV` together with Assumption V. Assumption IV.a is *not* among them. -/
structure AssumptionsII (E : Economy l m n) : Prop extends AssumptionsIIexceptV E where
  V : AssumptionV E

end ArrowDebreu.ThmII


