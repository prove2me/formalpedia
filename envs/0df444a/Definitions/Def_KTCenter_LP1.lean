-- Prove2me | Definitions.Def_KTCenter_LP1
-- name    : KTCenter_LP1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:28:44.561071+00:00
-- url     : https://prove2.me/theorems/e927fcd5-13f1-4f86-8432-f7cb0d385054
-- title:
--   Linear cost estimates, sample sequences with guesses, the sets $\mathcal P_\ell(g)$, $\mathcal P_{B,g}$, conditions (45), (54) and (LP1)
-- statement:
--   For a block $B$, marginals $x$ and keys $a\in P_v$, $s_{iv}(a,x)=\sum_{u\in B}\sum_{b\in P_u}q_i(v,a,u,b)x_{ub}$ (34), $G_{iB}(x)=\sum_{v\in B}\sum_{a}x_{va}(u'_{iv}(a)+s_{iv}(a,x)/2)$ (35) and $H_{iB}(x,\hat s)=\sum_{v\in B}\sum_a x_{va}(u'_{iv}(a)+\hat s_{iv}(a)/2)$ (36). A **sample sequence** $U_{B,1},\dots,U_{B,t}$ of members of $B$ with a guessed key $g(u)$ for each distinct sampled $u$ gives the estimate (40), (50)
--
--   $$\hat s_{iv}(a)=\frac{|B|}{t}\sum_{j=1}^{t}q_i\bigl(v,a,U_{B,j},g(U_{B,j})\bigr).$$
--
--   With $U_\ell=\bigcup\mathcal B_\ell$, $Q_\ell=\sum_{B\in\mathcal B_\ell}|B|^2$, $A=\kappa Q_\ell$ and $\Delta=\frac\kappa2\sum_{B\in\mathcal B'}|B|^2$ (33): $\mathcal P_\ell(g)$ is the set of nonnegative $(x,e)$ with (41)–(43); $\mathcal P_{B,g}$ the set of nonnegative $x$ with (51)–(52); (45) and (54) compare the estimates with $s^*_{iv}(a)=\sum_{u\in B}q_i(v,a,u,p^*_u)$ for an assignment $p^*$. (LP1), for a fixed $\varphi$ and large-subset member $g$, minimizes $t$ subject to (56)–(63):
--
--   $$A'_i+H^g_i(x)+\sum_{B\in\mathcal B_s}\sum_{h\in G_B}H_{iB,h}(y^{Bh})\le t\quad(\forall i),$$
--
--   the constraints of $\mathcal P_\ell(g)$, $\sum_h z_{Bh}=1$, $\sum_a y^{Bh}_{va}=z_{Bh}$, $|s_{iv}(a,y^{Bh})-z_{Bh}\hat s^{B,h}_{iv}(a)|\le\kappa|B|z_{Bh}$, and $x,e,y,z\ge0$.
--
--   **Formalization Note** Sample sequences are arbitrary here: Section 5 draws them at random and Section 6 reads them off walks, and none of the definitions depends on their origin. The small-subset families $G_B$ are lists of such members.
-- source:
--   Chakraborty, Das, Mukherjee, Kendall–tau Center Admits a PTAS, STOC 2027 submission (manuscript sha256 4739ffba…), §5.4–5.5, eqs. (33)–(36), (39)–(45), (50)–(54), (LP1) (56)–(63), pp.41–48 (PDF pp.43–50)

import Mathlib
import Definitions.Def_KTCenter_FixKeys

namespace KTCenter

namespace CostInstance

variable {K : ℕ} {C₀ C₁ : ℚ} (I : CostInstance K C₀ C₁) (ξ : ℚ)

/-- A real vector indexed by candidate–key pairs `(v, a)`, such as a marginal vector `x`. -/
abbrev Vec : Type := (v : Fin I.N) → Fin (I.k v) → ℝ

/-- `s_iv(a, x) = Σ_{u∈B} Σ_{b∈P_u} qᵢ(v, a, u, b) x_ub`, eq. (34), p.41 (PDF p.43).

Chakraborty, Das, Mukherjee, *Kendall–tau Center Admits a PTAS*, STOC 2027 submission (manuscript
sha256 4739ffba…), §5.4. -/
def sSum (B : Finset (Fin I.N)) (i : Fin I.n) (v : Fin I.N) (a : Fin (I.k v)) (x : I.Vec) : ℝ :=
  ∑ u ∈ B, ∑ b : Fin (I.k u), (I.q i v a u b : ℝ) * x u b

/-- `G_iB(x) = Σ_{v∈B} Σ_{a∈P_v} x_va (u′ᵢᵥ(a) + s_iv(a, x)/2)`, eq. (35), p.41. -/
noncomputable def GB (φ : I.AssignOn (I.F ξ)) (i : Fin I.n) (B : Finset (Fin I.N)) (x : I.Vec) : ℝ :=
  ∑ v ∈ B, ∑ a : Fin (I.k v), x v a * ((I.uprime ξ φ i v a : ℝ) + I.sSum B i v a x / 2)

/-- `H_iB(x, ŝ) = Σ_{v∈B} Σ_{a∈P_v} x_va (u′ᵢᵥ(a) + ŝ_iv(a)/2)`, eq. (36), p.42 (PDF p.44).

As on p.42, this is also used for nonnegative vectors that are not marginals. -/
noncomputable def HB (φ : I.AssignOn (I.F ξ)) (i : Fin I.n) (B : Finset (Fin I.N)) (x shat : I.Vec) : ℝ :=
  ∑ v ∈ B, ∑ a : Fin (I.k v), x v a * ((I.uprime ξ φ i v a : ℝ) + shat v a / 2)

/-- **A sample sequence for `B` with a guess on its distinct members**, p.42 (PDF p.44), and the
member records of §6.2, p.60: "a sample sequence and one guessed allowed key for each distinct
sampled candidate".

**Formalization Note.** The sequence is an arbitrary one here. §5.4 draws it at random and §6.2 takes
it from a walk, and the estimates (40), (50), the LP and Lemma 5.11 do not depend on where it came
from. -/
structure SampleGuess (B : Finset (Fin I.N)) where
  /-- the number of occurrences -/
  t : ℕ
  t_pos : 0 < t
  /-- the sampled candidates `U_{B,1}, …, U_{B,t}` -/
  seq : Fin t → Fin I.N
  seq_mem : ∀ j, seq j ∈ B
  /-- the guess `g ∈ 𝒫(S)` on the distinct sampled candidates -/
  guess : I.AssignOn (Finset.univ.image seq)

variable {I} in
/-- The estimate `ŝ_iv(a) = (|B|/t) Σ_{j=1}^t qᵢ(v, a, U_{B,j}, g(U_{B,j}))`, eqs. (40), (50),
pp.43, 46: every occurrence uses the same guessed key. -/
noncomputable def SampleGuess.estimate {B : Finset (Fin I.N)} (g : I.SampleGuess B) (i : Fin I.n) :
    I.Vec := fun v a =>
  ((B.card : ℝ) / (g.t : ℝ)) * ∑ j : Fin g.t,
    (I.q i v a (g.seq j)
      (g.guess ⟨g.seq j, Finset.mem_image_of_mem _ (Finset.mem_univ j)⟩) : ℝ)

variable {I} in
/-- The guess of `g` agrees with `p*` on the sampled candidates: `g = p*|_S`, pp.44, 47. -/
def SampleGuess.AgreesWith {ξ : ℚ} {B : Finset (Fin I.N)} (g : I.SampleGuess B)
    (pstar : I.AssignOn (I.Ures ξ)) : Prop :=
  ∀ (j : Fin g.t) (h : g.seq j ∈ I.Ures ξ),
    g.guess ⟨g.seq j, Finset.mem_image_of_mem _ (Finset.mem_univ j)⟩ = pstar ⟨g.seq j, h⟩

/-- `U_ℓ = ⋃_{B∈ℬ_ℓ} B`, p.43 (PDF p.45). -/
def Uell : Finset (Fin I.N) := (I.bLarge ξ).biUnion id

/-- `Q_ℓ = Σ_{B∈ℬ_ℓ} |B|²`, p.43. -/
def Qell : ℕ := ∑ B ∈ I.bLarge ξ, B.card ^ 2

/-- `A = κ Q_ℓ`, eq. (39), p.43.

**Formalization Note.** With no large subset, `Q_ℓ = 0`, so this is the printed `A = 0`. -/
def Aell : ℚ := I.kappa ξ * (I.Qell ξ : ℚ)

/-- `∆ = (κ/2) Σ_{B∈ℬ′} |B|²`, eq. (33), p.41. -/
def Delta : ℚ := I.kappa ξ / 2 * ((∑ B ∈ I.blocksRes ξ, B.card ^ 2 : ℕ) : ℚ)

/-- **A member of the joint large-subset family**: for each `B ∈ ℬ_ℓ` a sample sequence, and one
guess on the distinct sampled candidates. With `ℬ_ℓ = ∅` there is exactly one (empty) member, as on
p.43.

**Formalization Note.** The subsets of `ℬ_ℓ` are disjoint, so a guess per subset is one guess
`g ∈ 𝒫(S_ℓ)`. -/
abbrev LargeMember : Type := (B : {B // B ∈ I.bLarge ξ}) → I.SampleGuess B.1

/-- **The small-subset families** `G_B`, `B ∈ ℬ_s`, as lists. -/
abbrev SmallFamily : Type := (B : {B // B ∈ I.bSmall ξ}) → List (I.SampleGuess B.1)

variable {I ξ}

/-- `H^g_i(x) = Σ_{B∈ℬ_ℓ} H_iB(x, ŝ^g)`, eq. (44), p.43. -/
noncomputable def HLarge (φ : I.AssignOn (I.F ξ)) (g : I.LargeMember ξ) (i : Fin I.n) (x : I.Vec) : ℝ :=
  ∑ B : {B // B ∈ I.bLarge ξ}, I.HB ξ φ i B.1 x ((g B).estimate i)

/-- `G^ℓ_i(x) = Σ_{B∈ℬ_ℓ} G_iB(x)`, p.43. -/
noncomputable def GLarge (φ : I.AssignOn (I.F ξ)) (i : Fin I.n) (x : I.Vec) : ℝ :=
  ∑ B : {B // B ∈ I.bLarge ξ}, I.GB ξ φ i B.1 x

/-- `(x, e) ∈ 𝒫_ℓ(g)`: nonnegative vectors with eqs. (41)–(43), p.43 (PDF p.45). -/
def InPell (g : I.LargeMember ξ) (x : I.Vec) (e : Fin I.n → I.Vec) : Prop :=
  (∀ v ∈ I.Uell ξ, ∀ a, 0 ≤ x v a) ∧
  (∀ i, ∀ v ∈ I.Uell ξ, ∀ a, 0 ≤ e i v a) ∧
  (∀ v ∈ I.Uell ξ, ∑ a, x v a = 1) ∧
  (∀ (i : Fin I.n) (B : {B // B ∈ I.bLarge ξ}), ∀ v ∈ B.1, ∀ a,
    |I.sSum B.1 i v a x - (g B).estimate i v a| ≤ e i v a) ∧
  (∀ i, ∑ v ∈ I.Uell ξ, ∑ a, e i v a ≤ (I.Aell ξ : ℝ))

/-- `x ∈ 𝒫_{B,g}`: eqs. (51), (52), p.46 (PDF p.48). -/
def InPB {B : Finset (Fin I.N)} (g : I.SampleGuess B) (x : I.Vec) : Prop :=
  (∀ v ∈ B, ∀ a, 0 ≤ x v a) ∧
  (∀ v ∈ B, ∑ a, x v a = 1) ∧
  (∀ (i : Fin I.n), ∀ v ∈ B, ∀ a,
    |I.sSum B i v a x - g.estimate i v a| ≤ (I.kappa ξ : ℝ) * (B.card : ℝ))

/-- The integral marginals `x*_va = 1[p*_v = a]`, p.42 (PDF p.44). -/
def integralVec (pstar : I.AssignOn (I.Ures ξ)) : I.Vec := fun v a =>
  if h : v ∈ I.Ures ξ then (if pstar ⟨v, h⟩ = a then 1 else 0) else 0

/-- Condition (45), p.44 (PDF p.46):
`Σ_{v∈U_ℓ} Σ_{a∈P_v} |ŝ^g_iv(a) − s*_iv(a)| ≤ A` for every `i`.

**Formalization Note.** The sum over `U_ℓ` is written by blocks, since `ŝ` and `s*` at `v` are
those of the block of `v`, and `ℬ_ℓ` partitions `U_ℓ`. -/
def Cond45 (g : I.LargeMember ξ) (pstar : I.AssignOn (I.Ures ξ)) : Prop :=
  ∀ i : Fin I.n, ∑ B : {B // B ∈ I.bLarge ξ}, ∑ v ∈ B.1, ∑ a : Fin (I.k v),
    |(g B).estimate i v a - I.sSum B.1 i v a (integralVec pstar)| ≤ (I.Aell ξ : ℝ)

/-- Condition (54), p.47 (PDF p.49), for one small subset `B` and one member `h`:
`|ŝ^{B,h}_iv(a) − s*_iv(a)| ≤ κ|B|` for all `i`, `v ∈ B`, `a ∈ P_v`. -/
def Cond54 {B : Finset (Fin I.N)} (h : I.SampleGuess B) (pstar : I.AssignOn (I.Ures ξ)) : Prop :=
  ∀ (i : Fin I.n), ∀ v ∈ B, ∀ a,
    |h.estimate i v a - I.sSum B i v a (integralVec pstar)| ≤ (I.kappa ξ : ℝ) * (B.card : ℝ)

variable (I ξ) in
/-- **The variables of (LP1)**, p.48 (PDF p.50): `x`, `e`, `y^{Bh}`, `z_{Bh}`, `t`. -/
structure LPPoint (fam : I.SmallFamily ξ) where
  /-- `x_va` for `v ∈ U_ℓ` -/
  x : I.Vec
  /-- `e_iva` for `v ∈ U_ℓ` -/
  e : Fin I.n → I.Vec
  /-- `y^{Bh}_va` for `v ∈ B ∈ ℬ_s` -/
  y : (B : {B // B ∈ I.bSmall ξ}) → Fin (fam B).length → I.Vec
  /-- `z_{Bh}` -/
  z : (B : {B // B ∈ I.bSmall ξ}) → Fin (fam B).length → ℝ
  /-- `t` -/
  t : ℝ

/-- The estimated cost on the left of (56): `A′ᵢ + H^g_i(x) + Σ_{B∈ℬ_s} Σ_{h∈G_B} H_{iB,h}(y^{Bh})`. -/
noncomputable def lpCost (φ : I.AssignOn (I.F ξ)) (g : I.LargeMember ξ) {fam : I.SmallFamily ξ}
    (P : I.LPPoint ξ fam) (i : Fin I.n) : ℝ :=
  (I.Aprime ξ φ i : ℝ) + HLarge φ g i P.x +
    ∑ B : {B // B ∈ I.bSmall ξ}, ∑ h : Fin (fam B).length,
      I.HB ξ φ i B.1 (P.y B h) (((fam B).get h).estimate i)

/-- **Feasibility for (LP1)**, eqs. (56)–(63), p.48 (PDF p.50), for the pair `(φ, g)`.

(57)–(59) with `x, e ≥ 0` are `InPell`, as noted on p.49.

**Formalization Note.** Sign conditions and constraints are imposed exactly on the printed index
ranges, so values of the vectors off these ranges play no role. -/
def IsFeasible (φ : I.AssignOn (I.F ξ)) (g : I.LargeMember ξ) {fam : I.SmallFamily ξ}
    (P : I.LPPoint ξ fam) : Prop :=
  (∀ i, lpCost φ g P i ≤ P.t) ∧
  InPell g P.x P.e ∧
  (∀ B, ∑ h, P.z B h = 1) ∧
  (∀ B h, ∀ v ∈ B.1, ∑ a, P.y B h v a = P.z B h) ∧
  (∀ (i : Fin I.n) (B : {B // B ∈ I.bSmall ξ}) (h : Fin (fam B).length), ∀ v ∈ B.1, ∀ a,
    |I.sSum B.1 i v a (P.y B h) - P.z B h * ((fam B).get h).estimate i v a| ≤
      (I.kappa ξ : ℝ) * (B.1.card : ℝ) * P.z B h) ∧
  (∀ B h, ∀ v ∈ B.1, ∀ a, 0 ≤ P.y B h v a) ∧
  (∀ B h, 0 ≤ P.z B h)

end CostInstance

end KTCenter


