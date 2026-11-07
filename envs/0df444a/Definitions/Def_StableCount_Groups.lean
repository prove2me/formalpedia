-- Prove2me | Definitions.Def_StableCount_Groups
-- name    : StableCount_Groups
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:51:21.909688+00:00
-- url     : https://prove2.me/theorems/17e3226b-72a3-4e1a-ac66-d18976f3b0fa
-- title:
--   Supports, first groups, Table 1, $U$, $\Delta$, $D^*_A$ and the sets $\mathcal P_5$, $\mathcal P_0$, $Z_A$
-- statement:
--   For a rotation $\rho$ of $Q$, the **support** is $S(\rho)=\{v\in V:b_v\preceq\rho\}$, with $s(\rho)=|S(\rho)|$, and the **support excess** of one sex is
--   $$
--   \Omega=\sum_{v\in V}\sum_{r=1}^{d_v}\big(s(\rho_{v,r})-r-1\big)h_r.
--   $$
--   The **first group** of $\rho$ is $V_\rho=\{v\in V:b_v=\rho\}$. An *initial swap* is a swap that is the first rotation of both participants. An *exceptional swap* is a rotation $B$ with $V_B=\{x\}$ and $s(B)=3$, and $x$ is then exceptional. An *ordinary* rotation is any other rotation with $V_\rho\ne\emptyset$. With $d=d_v$ and $k$ the size of $v$'s first group, the reserved amount $\beta_v$ is, by Table 1,
--
--   | Person | $\beta_v$ |
--   |---|---|
--   | Ordinary, $k\ge 3$ | $H_d+h_1$ |
--   | Ordinary, $k=1,2$ | $H_d+2h_1+h_2\mathbf 1_{d\ge 2}$ |
--   | Exceptional | $H_d+h_1+h_2\mathbf 1_{d\ge 2}$ |
--   | Participant in an initial swap with an associated exceptional person | $H_d$ |
--   | Participant in an initial swap without an associated exceptional person | $H_d+h_2\mathbf 1_{d\ge 2}$ |
--
--   Further, $U=\sum_v H_{d_v}+\Omega-\sum_v\beta_v$ and $\Delta_\rho=\sum_{v\in V_\rho}\beta_v-|V_\rho|\lambda(p(\rho))$. For an initial swap $A=(u,v)$, $X_A$ is the set of exceptional labels associated with $A$, $K_A=\{u,v\}\cup X_A$, $N^s_A=|\{x\in X_A:d^s_x\ge 2\}|$, and
--   $$
--   D^*_A=2\lambda(p^*(A))+\sum_{x\in X_A}\lambda(p^*(b_x))-\frac12\sum_{v\in K_A}(\beta^m_v+\beta^w_v).
--   $$
--   $\mathcal P_5$ is the set of initial swaps having an association triple inside $S(\rho)$ for some ordinary $\rho$ with $s(\rho)\ge 5$, and $\mathcal P_0$ is the rest. $Z_A$ is the set of labels $z$ with $b_z$ ordinary whose support contains an association triple of $A$. With $b=h_2$, for one sex, $E_x=\sum_{r=2}^{\min\{d_x,3\}}(s(\rho_{x,r})-4)h_r$, $T_z=\Delta_{b_z}$ if $d_z=1$ and $T_z=\Delta_{b_z}+b(s(\rho_{z,2})-4)$ if $d_z\ge 2$, and $R_A=\sum_{x\in X_A}E_x+\sum_{z\in Z_A}T_z$.
--
--   This is the accounting by which the proof of the branching criterion covers the cost of each label.
--
--   **Formalization Note** All subtraction is in `ℝ`. The parent is per sex: for $B=(u,x)$ after $A=(u,v)$ the men's parent of $x$ is $u$ and the women's is the woman with label $v$, which is how the proof of Lemma 6.2 reads Table 1. Support, $X_A$, $\mathcal P_5$, $\mathcal P_0$ and $Z_A$ are free of sex. Sums over $\rho_{v,r}$ are sums over the rotations of the person's chain with their ranks.
-- source:
--   Ghorbani, Mnich, A 2.81^n upper bound on the number of stable matchings, arXiv:2611.06494 (held PDF sha256 9445f6a8…), (8), p.16; (10), p.17; §5.2, p.17; §5.3, p.18; Table 1, p.19; (14), (16), p.20; §5.4, §6, p.21; §8, p.28

import Mathlib
import Definitions.Def_StableCount_Potential

namespace StableCount

variable {n : ℕ}

namespace Member

variable (Q : Member n)

/-- `b_v = i`: rotation `i` is the first rotation of the active label `v` (arXiv:2611.06494, held PDF
sha256 9445f6a8…, §4.2, p.15). -/
def IsFirst (v : Fin n) (i : Fin Q.R) : Prop := ∃ hv : v ∈ Q.V, Q.first v hv = i

open Classical in
/-- `S(ρ) = {v ∈ V : b_v ⪯ ρ}`, the support of `ρ`, display (8) (arXiv:2611.06494, held PDF sha256
9445f6a8…, (8), p.16). It is free of sex: it uses man labels and `b_v`. -/
noncomputable def support (i : Fin Q.R) : Finset (Fin n) :=
  Finset.univ.filter fun v => ∃ j, Q.IsFirst v j ∧ Q.le j i

/-- `s(ρ) = |S(ρ)|` (arXiv:2611.06494, held PDF sha256 9445f6a8…, §5.1, p.16). -/
noncomputable def s (i : Fin Q.R) : ℕ := (Q.support i).card

/-- The summand of the support excess at the occurrence of the person with label `v` in rotation
`i`, of rank `r`: `(s(ρ_{v,r}) − r − 1) h_r` (arXiv:2611.06494, held PDF sha256 9445f6a8…, (10), p.17).
All subtraction is in `ℝ`. -/
noncomputable def omegaTerm (h : ℕ → ℝ) (x : Sex) (v : Fin n) (i : Fin Q.R) : ℝ :=
  ((Q.s i : ℝ) - (Q.rank x (Q.person x v) i : ℝ) - 1) * h (Q.rank x (Q.person x v) i)

/-- `Ω = ∑_{v∈V} ∑_{r=1}^{d_v} (s(ρ_{v,r}) − r − 1) h_r`, the support excess of sex `x`, display (10)
(arXiv:2611.06494, held PDF sha256 9445f6a8…, (10), p.17).

**Formalization Note** The inner sum runs over the rotations `ρ_{v,r}` of the person's chain, each with
its rank `r`, which is the same sum as over `r = 1, …, d_v`. -/
noncomputable def Omega (h : ℕ → ℝ) (x : Sex) : ℝ :=
  ∑ v ∈ Q.V, ∑ i ∈ Q.chainOf x (Q.person x v), Q.omegaTerm h x v i

open Classical in
/-- `V_ρ = {v ∈ V : b_v = ρ}`, the first group of `ρ` (arXiv:2611.06494, held PDF sha256 9445f6a8…,
§5.2, p.17). -/
noncomputable def firstGroup (i : Fin Q.R) : Finset (Fin n) :=
  Finset.univ.filter fun v => Q.IsFirst v i

/-- The man labels participating in rotation `i` (arXiv:2611.06494, held PDF sha256 9445f6a8…, §3,
p.12). -/
def participants (i : Fin Q.R) : Finset (Fin n) := Finset.univ.filter fun v => Q.moves .man i v

/-- An initial swap: a swap `A = (u, v)` that is the first rotation of both participants, so
`V_A = {u, v}` (arXiv:2611.06494, held PDF sha256 9445f6a8…, §5.3, p.18). -/
def IsInitialSwap (i : Fin Q.R) : Prop :=
  (Q.participants i).card = 2 ∧ ∀ v ∈ Q.participants i, Q.IsFirst v i

/-- An exceptional swap: a rotation `B` with `V_B = {x}` and `s(B) = 3` (arXiv:2611.06494, held PDF
sha256 9445f6a8…, §5.3, p.18). -/
def IsExceptionalSwap (i : Fin Q.R) : Prop := (Q.firstGroup i).card = 1 ∧ Q.s i = 3

/-- An ordinary rotation: a rotation `ρ` with `V_ρ ≠ ∅` that is neither an initial swap nor an
exceptional swap (arXiv:2611.06494, held PDF sha256 9445f6a8…, §5.3, p.18). -/
def IsOrdinary (i : Fin Q.R) : Prop :=
  (Q.firstGroup i).Nonempty ∧ ¬ Q.IsInitialSwap i ∧ ¬ Q.IsExceptionalSwap i

/-- The label `x` is exceptional: its first rotation is an exceptional swap (arXiv:2611.06494, held
PDF sha256 9445f6a8…, §5.3, p.18). -/
def IsExceptional (x : Fin n) : Prop := ∃ i, Q.IsFirst x i ∧ Q.IsExceptionalSwap i

/-- In sex `s`, the label `u` is the parent of the exceptional label `x`: `u` is the participant of
`b_x` in the description of that sex other than `x` (arXiv:2611.06494, held PDF sha256 9445f6a8…,
§5.3, p.18; Lemma 6.2's proof, pp.23–24).

**Formalization Note** The parent depends on the sex. After `A = (u, v)` and `B = (u, x)`, man `u` is
the men's parent of `x`, and the woman with label `v` is the women's parent (p.23: "the degrees of its
parent in the men's and women's descriptions"). Table 1 is read per sex. -/
def IsParent (s : Sex) (x u : Fin n) : Prop :=
  Q.IsExceptional x ∧ u ≠ x ∧ ∃ i, Q.IsFirst x i ∧ Q.moves s i (Q.person s u)

open Classical in
/-- `β_v`, the amount reserved for the person of sex `s` with label `v`: Table 1
(arXiv:2611.06494, held PDF sha256 9445f6a8…, Table 1, p.19). Here `d = d_v` and `k` is the size of
`v`'s first group.

| Person | `β_v` |
|---|---|
| Ordinary, `k ≥ 3` | `H_d + h₁` |
| Ordinary, `k = 1, 2` | `H_d + 2h₁ + h₂ 1_{d≥2}` |
| Exceptional | `H_d + h₁ + h₂ 1_{d≥2}` |
| In an initial swap, with an associated exceptional person | `H_d` |
| In an initial swap, without one | `H_d + h₂ 1_{d≥2}` |

**Formalization Note** The last two rows are the remaining active labels: a first rotation is an
initial swap, an exceptional swap or ordinary. They depend on whether the person is a parent in that
sex. -/
noncomputable def beta (h : ℕ → ℝ) (s : Sex) (v : Fin n) : ℝ :=
  let d := Q.dL s v
  let extra : ℝ := if 2 ≤ d then h 2 else 0
  if ∃ i, Q.IsFirst v i ∧ Q.IsOrdinary i then
    if ∃ i, Q.IsFirst v i ∧ 3 ≤ (Q.firstGroup i).card then Hsum h d + h 1
    else Hsum h d + 2 * h 1 + extra
  else if Q.IsExceptional v then Hsum h d + h 1 + extra
  else if ∃ x, Q.IsParent s x v then Hsum h d
  else Hsum h d + extra

/-- `U_s = ∑_{v∈V} H_{dˢ_v} + Ω_s − ∑_{v∈V} βˢ_v`, the unreserved occurrence surplus, as in (14)
(arXiv:2611.06494, held PDF sha256 9445f6a8…, §5.4, p.21). -/
noncomputable def U (h : ℕ → ℝ) (s : Sex) : ℝ :=
  ∑ v ∈ Q.V, Hsum h (Q.dL s v) + Q.Omega h s - ∑ v ∈ Q.V, Q.beta h s v

/-- `∆ˢ_ρ = ∑_{v∈V_ρ} βˢ_v − |V_ρ| λ(pˢ(ρ))`, the unused amount of a first group, display (16)
(arXiv:2611.06494, held PDF sha256 9445f6a8…, (16), p.20). -/
noncomputable def Delta (h : ℕ → ℝ) (s : Sex) (i : Fin Q.R) : ℝ :=
  ∑ v ∈ Q.firstGroup i, Q.beta h s v - ((Q.firstGroup i).card : ℝ) * lam (Q.pLoss h s i)

open Classical in
/-- `𝒫`, the set of initial swaps (arXiv:2611.06494, held PDF sha256 9445f6a8…, §5.3, p.20). -/
noncomputable def initialSwaps : Finset (Fin Q.R) := Finset.univ.filter fun i => Q.IsInitialSwap i

open Classical in
/-- `𝒪`, the set of ordinary rotations (arXiv:2611.06494, held PDF sha256 9445f6a8…, §5.3, p.20). -/
noncomputable def ordinary : Finset (Fin Q.R) := Finset.univ.filter fun i => Q.IsOrdinary i

open Classical in
/-- `X_A`, the set of exceptional labels associated with the initial swap `A`: those whose exceptional
swap `b_x` follows `A` (arXiv:2611.06494, held PDF sha256 9445f6a8…, §5.3, p.20).

**Formalization Note** By Lemma 5.4, `↓b_x = {A', b_x}` for a single initial swap `A'`, so "`A`
strictly precedes `b_x`" is the source's association. -/
noncomputable def XA (A : Fin Q.R) : Finset (Fin n) :=
  Finset.univ.filter fun x => Q.IsExceptional x ∧ ∃ i, Q.IsFirst x i ∧ Q.le A i ∧ A ≠ i

/-- `K_A = {u, v} ∪ X_A`, for `A = (u, v)`, where `{u, v} = V_A` (arXiv:2611.06494, held PDF sha256
9445f6a8…, §5.3, p.20). -/
noncomputable def KA (A : Fin Q.R) : Finset (Fin n) := Q.firstGroup A ∪ Q.XA A

/-- `D*_A = 2λ(p*(A)) + ∑_{x∈X_A} λ(p*(b_x)) − ½ ∑_{v∈K_A} (βᵐ_v + βʷ_v)` (arXiv:2611.06494, held PDF
sha256 9445f6a8…, §5.3, p.20). -/
noncomputable def DStar (h : ℕ → ℝ) (A : Fin Q.R) : ℝ :=
  2 * lam (Q.pStar h A) + ∑ x ∈ Q.XA A, Q.atFirst (fun i => lam (Q.pStar h i)) x -
    (1 / 2) * ∑ v ∈ Q.KA A, (Q.beta h .man v + Q.beta h .woman v)

open Classical in
/-- `Nˢ_A = |{x ∈ X_A : dˢ_x ≥ 2}|` (arXiv:2611.06494, held PDF sha256 9445f6a8…, §6, p.21). -/
noncomputable def NA (s : Sex) (A : Fin Q.R) : ℕ :=
  ((Q.XA A).filter fun x => 2 ≤ Q.dL s x).card

/-- `S` contains an association triple of `A`: a set `{u, v, x}` with `A = (u, v)`, `x ∈ X_A`
(arXiv:2611.06494, held PDF sha256 9445f6a8…, §5.3, p.18: "For an exceptional swap `B = (u, x)`
following `A = (u, v)`, we call `{u, v, x}` its association triple"). -/
def HasTripleIn (A : Fin Q.R) (S : Finset (Fin n)) : Prop :=
  ∃ x ∈ Q.XA A, Q.firstGroup A ∪ {x} ⊆ S

open Classical in
/-- `𝒫₅`: the initial swaps having an association triple contained in `S(ρ)` for some ordinary rotation
`ρ` with `s(ρ) ≥ 5` (arXiv:2611.06494, held PDF sha256 9445f6a8…, §8, p.28). -/
noncomputable def P5 : Finset (Fin Q.R) :=
  Q.initialSwaps.filter fun A => ∃ i, Q.IsOrdinary i ∧ 5 ≤ Q.s i ∧ Q.HasTripleIn A (Q.support i)

/-- `𝒫₀ = 𝒫 \ 𝒫₅` (arXiv:2611.06494, held PDF sha256 9445f6a8…, §8, p.28). -/
noncomputable def P0 : Finset (Fin Q.R) :=
  Q.initialSwaps \ Q.P5

open Classical in
/-- `Z_A`: the labels `z` whose first rotation `b_z` is ordinary and whose support `S(b_z)` contains an
association triple of `A` (arXiv:2611.06494, held PDF sha256 9445f6a8…, §8, p.28). -/
noncomputable def ZA (A : Fin Q.R) : Finset (Fin n) :=
  Finset.univ.filter fun z => ∃ i, Q.IsFirst z i ∧ Q.IsOrdinary i ∧ Q.HasTripleIn A (Q.support i)

/-- `E_x = ∑_{r=2}^{min{d_x,3}} (s(ρ_{x,r}) − 4) h_r`, for sex `s` (arXiv:2611.06494, held PDF sha256
9445f6a8…, §8, p.28).

**Formalization Note** The sum runs over the rotations of the person's chain with rank `2` or `3`, which
is the printed range. -/
noncomputable def Ex (h : ℕ → ℝ) (s : Sex) (x : Fin n) : ℝ :=
  ∑ i ∈ (Q.chainOf s (Q.person s x)).filter
      (fun i => 2 ≤ Q.rank s (Q.person s x) i ∧ Q.rank s (Q.person s x) i ≤ 3),
    ((Q.s i : ℝ) - 4) * h (Q.rank s (Q.person s x) i)

/-- `T_z = ∆_{b_z}` if `d_z = 1`, and `T_z = ∆_{b_z} + b (s(ρ_{z,2}) − 4)` if `d_z ≥ 2`, with `b = h₂`,
for sex `s` (arXiv:2611.06494, held PDF sha256 9445f6a8…, §8, p.28).

**Formalization Note** The second term is a sum over the rotations of rank `2` on the person's chain:
there is one if `d_z ≥ 2`, and none if `d_z = 1`. -/
noncomputable def Tz (h : ℕ → ℝ) (s : Sex) (z : Fin n) : ℝ :=
  Q.atFirst (Q.Delta h s) z +
    ∑ i ∈ (Q.chainOf s (Q.person s z)).filter (fun i => Q.rank s (Q.person s z) i = 2),
      h 2 * ((Q.s i : ℝ) - 4)

/-- `R_A = ∑_{x∈X_A} E_x + ∑_{z∈Z_A} T_z`, for sex `s` (arXiv:2611.06494, held PDF sha256 9445f6a8…,
§8, p.28). -/
noncomputable def RA (h : ℕ → ℝ) (s : Sex) (A : Fin Q.R) : ℝ :=
  ∑ x ∈ Q.XA A, Q.Ex h s x + ∑ z ∈ Q.ZA A, Q.Tz h s z

end Member

end StableCount


