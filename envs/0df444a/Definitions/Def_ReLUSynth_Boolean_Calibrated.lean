-- Prove2me | Definitions.Def_ReLUSynth_Boolean_Calibrated
-- name    : ReLUSynth_Boolean_Calibrated
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T00:09:24.972656+00:00
-- url     : https://prove2.me/theorems/cf61662d-ad7e-428a-8739-1f58abc37604
-- title:
--   The calibrated threshold construction of §4.2: constants, coordinates, inventory, target, formal expansions, query target and common-ramp networks
-- statement:
--   Fix source numbers $\beta_1,\dots,\beta_n$, a target $T$, a prime $q$, $p=q-1$, and choices $r,F,M$. Put $Q=2^r-1$, $n_a=p+3$, $K=2n+3p+14$, $J=K+1$, $R=3Jr$, $d=n+n_a+R+1$, $P=FQ$, $m=K+2R$, $H_0=16q^4(64(m+1)^4P^4+1)$, $w=M^{-1}$, $\Gamma=M^9$, $s_0=1/(q\Gamma)$. The construction is **valid** when $q\ge5$ is prime, $0<\beta_j<T$, no $\beta_j$ is a power of two, $\beta_j\equiv3$ and $T\equiv0\pmod q$, $n>p$, $r>q$ is prime with $Q>8(T+\sum_j\beta_j+2)^2$, $F$ is a power of two with $F>\max\{8Q^4,4d+64q^2+8\}$, and $M$ is a power of two with $M>\max\{2H_0,q(2R+3)\}$.
--
--   The $d$ **coordinates** are $n$ source bits, $n_a$ anchor bits, $J$ query blocks with three copies at each level $i\in\{0,\dots,r-1\}$, and a control bit; their **baselines** are $F\beta_j$, $B=F(Q-T)-w$, $F2^i+2w$ and $C=P-\tfrac32w$. The **inventory** has two occurrences of every baseline, $p$ of $s_0$, two of $\Gamma$, and one each of $+M,-M,-(P-w),-P$ ($m$ occurrences). The **target** is
--   $$f(x)=1\iff\Lambda(x)=\sum_t\lambda_tx_t\ \ge\ P-w .$$
--   The **formal expansion** of an occurrence is a Laurent polynomial in $w,\Gamma$ over $\mathbb Q$: $F\nu+\delta w$ for a finite primitive ($\delta=0,-1,2,-\tfrac32$ for source, anchor, query, control baselines; $\delta=1$ for $-(P-w)$, $0$ for $-P$), $\Gamma$, $q^{-1}\Gamma^{-1}$ for $s_0$, and $\pm w^{-1}$ for $\pm M$.
--
--   The **query target** on $3r$ coordinates is $g(y)=1\iff\sum_i\sum_\gamma2^iy_{i,\gamma}\ge Q$. A **common-ramp** candidate chooses the occurrences of the two sharing edges (weight $a$), of the two direct input edges of each input (weight $b_j$), and of the optional sharing wire $u(x)=\rho(v_b+\sum_jv_jx_j)$; its network is
--   $$N(x)=D\big(\rho(S(x)-(P-w))-\rho(S(x)-P)\big),\qquad S(x)=a\,u(x)+\sum_jb_jx_j,\quad D=M,$$
--   with hinge biases $-(P-w),-P$ and gains $\pm D$ on their supplied occurrences and no other output contribution. It is **legal** when this network is permitted (at-most-once, cap four), every used sharing, direct and wire occurrence is positive, paired occurrences have identical values, and the wire is omitted when there is no sharing edge.
-- source:
--   Myrisiotis, The Complexity of ReLU Network Synthesis from a Parameter Multiset, arXiv:2611.04074v1, pp. 19–20, §4.2; p. 21, §4.3; p. 22, Lemma 4.7; pp. 23–24, Lemma 4.9

import Mathlib
import Definitions.Def_ReLUSynth_Boolean_Network

namespace ReLUSynth.Boolean

/-! Myrisiotis, *The Complexity of ReLU Network Synthesis from a Parameter Multiset*,
arXiv:2611.04074v1, §4.2 "A Calibrated Threshold Construction" (pp. 19–20), the formal
expansions of §4.3 (p. 21), the query target of Lemma 4.7 (p. 22) and the common-ramp networks of
Lemma 4.9 (pp. 23–24). -/

/-- The data of the calibrated construction (§4.2, pp. 19–20): a source blocker instance
`β_1, …, β_n, T` with its prime `q` (budget `p = q − 1`), and the numerical choices `r`, `F`, `M`.
The conditions the page imposes on them are `CalibData.Valid`. -/
structure CalibData where
  /-- the number of source numbers -/
  n : ℕ
  /-- the source numbers `β_1, …, β_n` -/
  β : Fin n → ℕ
  /-- the target `T` -/
  T : ℕ
  /-- the supplied prime `q` -/
  q : ℕ
  /-- the chosen odd prime `r > q` -/
  r : ℕ
  /-- the chosen power of two `F` -/
  F : ℕ
  /-- the chosen power of two `M` -/
  M : ℕ

namespace CalibData

variable (c : CalibData)

/-- `p = q − 1`. -/
def p : ℕ := c.q - 1
/-- `Q = 2^r − 1`. -/
def Q : ℕ := 2 ^ c.r - 1
/-- `n_a = p + 3`, the number of anchor bits. -/
def na : ℕ := c.p + 3
/-- `K = 2n + 3p + 14`. -/
def K : ℕ := 2 * c.n + 3 * c.p + 14
/-- `J = K + 1`, the number of query blocks. -/
def J : ℕ := c.K + 1
/-- `R = 3Jr`, the number of query coordinates. -/
def R : ℕ := 3 * c.J * c.r
/-- `d = n + n_a + R + 1`, the input dimension. -/
def d : ℕ := c.n + c.na + c.R + 1
/-- `P = FQ`. -/
def P : ℕ := c.F * c.Q
/-- `m = K + 2R`, the inventory size. -/
def m : ℕ := c.K + 2 * c.R
/-- `H_0 = 16q^4(64(m+1)^4 P^4 + 1)`. -/
def H0 : ℕ := 16 * c.q ^ 4 * (64 * (c.m + 1) ^ 4 * c.P ^ 4 + 1)

/-- **The conditions of §4.2** (pp. 19–20). The source instance is in the hardness family of
Lemma 4.5: `q ≥ 5` prime, `0 < β_j < T`, no `β_j` a power of two, `β_j ≡ 3`, `T ≡ 0 (mod q)`,
`n > p`. The choices: `r` a prime with `r > q` and `Q = 2^r − 1 > 8(T + ∑_j β_j + 2)^2`; `F` a
power of two with `F > max{8Q^4, 4d + 64q^2 + 8}`; `M` a power of two with
`M > max{2H_0, q(2R + 3)}`. ("Odd" for the primes `q ≥ 5` and `r > q` is implied.) -/
def Valid : Prop :=
  c.q.Prime ∧ 5 ≤ c.q ∧
  (∀ j, 0 < c.β j ∧ c.β j < c.T ∧ (¬ ∃ k : ℕ, c.β j = 2 ^ k) ∧ c.β j % c.q = 3) ∧
  c.T % c.q = 0 ∧ c.p < c.n ∧
  c.r.Prime ∧ c.q < c.r ∧ 8 * (c.T + ∑ j, c.β j + 2) ^ 2 < c.Q ∧
  (∃ e : ℕ, c.F = 2 ^ e) ∧ 8 * c.Q ^ 4 < c.F ∧ 4 * c.d + 64 * c.q ^ 2 + 8 < c.F ∧
  (∃ e : ℕ, c.M = 2 ^ e) ∧ 2 * c.H0 < c.M ∧ c.q * (2 * c.R + 3) < c.M

/-- `w = M^{-1}`. -/
def w : ℚ := 1 / (c.M : ℚ)
/-- `Γ = M^9`. -/
def Γ : ℚ := (c.M : ℚ) ^ 9
/-- `s_0 = 1/(qΓ)`, the selector value. -/
def s0 : ℚ := 1 / ((c.q : ℚ) * c.Γ)

end CalibData

/-- The `d` input coordinates of the construction (p. 20): `n` source bits `z_j`, `n_a` anchor
bits `a_h`, `J` query blocks with three copies `γ` at every level `i ∈ {0, …, r − 1}`, and one
control bit `c`. -/
inductive Coord (c : CalibData) where
  | source (j : Fin c.n)
  | anchor (h : Fin c.na)
  | query (b : Fin c.J) (i : Fin c.r) (γ : Fin 3)
  | control
  deriving DecidableEq, Fintype

/-- The inventory occurrences of the construction (p. 20): two occurrences of every coordinate's
baseline, `p` occurrences of `s_0` (the selectors), two of `Γ`, and one each of the four signed
parameters `+M, −M, −(P − w), −P`. -/
inductive Occ (c : CalibData) where
  | base (t : Coord c) (k : Fin 2)
  | sel (k : Fin c.p)
  | gam (k : Fin 2)
  | gainPos
  | gainNeg
  | biasHi
  | biasLo
  deriving DecidableEq, Fintype

namespace CalibData

variable (c : CalibData)

/-- The baseline `λ_t` of coordinate `t` (p. 20): `Fβ_j` (source), `B = F(Q − T) − w` (anchor),
`F2^i + 2w` (level-`i` query), `C = P − (3/2)w` (control). -/
def baseline : Coord c → ℚ
  | .source j => (c.F : ℚ) * c.β j
  | .anchor _ => (c.F : ℚ) * ((c.Q : ℚ) - c.T) - c.w
  | .query _ i _ => (c.F : ℚ) * 2 ^ i.val + 2 * c.w
  | .control => (c.P : ℚ) - 3 / 2 * c.w

/-- **The calibrated inventory** `W`: the value of each occurrence (p. 20). -/
def inv : Occ c → ℚ
  | .base t _ => c.baseline t
  | .sel _ => c.s0
  | .gam _ => c.Γ
  | .gainPos => (c.M : ℚ)
  | .gainNeg => -(c.M : ℚ)
  | .biasHi => -((c.P : ℚ) - c.w)
  | .biasLo => -(c.P : ℚ)

/-- The real values of the inventory occurrences. -/
noncomputable def invR (o : Occ c) : ℝ := (c.inv o : ℝ)

/-- The baseline score `Λ(x) = ∑_t λ_t x_t` of a Boolean input (p. 20). -/
def score (x : Coord c → Bool) : ℚ := ∑ t, c.baseline t * (if x t then 1 else 0)

/-- **The calibrated target** `f(x) = 1 ⟺ Λ(x) ≥ P − w` (p. 20). -/
def target (x : Coord c → Bool) : Bool := decide ((c.P : ℚ) - c.w ≤ c.score x)

/-- The query coordinates of block `b` set to `y`, every other coordinate zero (Lemma 4.7). -/
def blockEmbed (b : Fin c.J) (y : Fin c.r × Fin 3 → Bool) : Coord c → Bool
  | .query b' i γ => if b' = b then y (i, γ) else false
  | _ => false

end CalibData

/-- The ring `ℚ[w^{±1}, Γ^{±1}]` of Laurent polynomials in two formal variables with rational
coefficients (§4.3, p. 21): the monomial `w^i Γ^j` is `AddMonoidAlgebra.single (i, j) 1`. -/
abbrev Laurent2 := AddMonoidAlgebra ℚ (ℤ × ℤ)

/-- The monomial `c · w^i Γ^j`. -/
noncomputable def lmono (i j : ℤ) (a : ℚ) : Laurent2 := AddMonoidAlgebra.single (i, j) a

namespace CalibData

variable (c : CalibData)

/-- **The formal expansion of an inventory value** (§4.3, p. 21): a finite primitive `Fν + δw`
expands as `Fν + δ·w`; `Γ` as the monomial `Γ`; `s_0` as `q^{-1} Γ^{-1}`; the gains `±M` as
`±w^{-1}`. Here `δ` is `0` for a source baseline and for `−P`, `−1` for `B`, `2` for a query
baseline, `−3/2` for `C`, and `1` for `−(P − w)`. -/
noncomputable def formal : Occ c → Laurent2
  | .base (.source j) _ => lmono 0 0 ((c.F : ℚ) * c.β j)
  | .base (.anchor _) _ => lmono 0 0 ((c.F : ℚ) * ((c.Q : ℚ) - c.T)) + lmono 1 0 (-1)
  | .base (.query _ i _) _ => lmono 0 0 ((c.F : ℚ) * 2 ^ i.val) + lmono 1 0 2
  | .base .control _ => lmono 0 0 (c.P : ℚ) + lmono 1 0 (-3 / 2)
  | .sel _ => lmono 0 (-1) (1 / (c.q : ℚ))
  | .gam _ => lmono 0 1 1
  | .gainPos => lmono (-1) 0 1
  | .gainNeg => lmono (-1) 0 (-1)
  | .biasHi => lmono 0 0 (-(c.P : ℚ)) + lmono 1 0 1
  | .biasLo => lmono 0 0 (-(c.P : ℚ))

end CalibData

/-- **The query target** `g` of Lemma 4.7 (p. 22) on the `3r` coordinates `y_{i,γ}` (level
`i ∈ {0, …, r − 1}`, copy `γ ∈ {1, 2, 3}`): `g(y) = 1 ⟺ ∑_i ∑_γ 2^i y_{i,γ} ≥ Q = 2^r − 1`. -/
def queryTarget (r : ℕ) (y : Fin r × Fin 3 → Bool) : Bool :=
  decide (2 ^ r - 1 ≤ ∑ p : Fin r × Fin 3, 2 ^ p.1.val * (if y p then 1 else 0))

/-- **A common-ramp candidate** for the calibrated inventory (Lemma 4.9, pp. 23–24): the
occurrences of the two sharing edges of weight `a` (absent: `none`), the two direct input edges
of weight `b_j` of each input `x_j`, and the bias `v_b` and input edges `v_j` of the optional
sharing wire `u(x) = ρ(v_b + ∑_j v_j x_j)`. The hinge biases `−(P − w)`, `−P` and the output gains
`+D, −D` (`D = M`) use their supplied occurrences. -/
structure CommonRamp (c : CalibData) where
  /-- the occurrences on the sharing edges wire → hinge 1, wire → hinge 2 -/
  share : Option (Occ c × Occ c)
  /-- the occurrences on the direct input edges `x_j` → hinge 1, `x_j` → hinge 2 -/
  direct : Coord c → Option (Occ c × Occ c)
  /-- the occurrence of the wire bias `v_b` -/
  wireBias : Option (Occ c)
  /-- the occurrences of the wire's input edges `v_j` -/
  wireIn : Coord c → Option (Occ c)

namespace CommonRamp

variable {c : CalibData}

/-- **The network of a common-ramp candidate.** With a sharing wire: computational vertices
`0` = wire `u`, `1` = hinge with bias `−(P − w)`, `2` = hinge with bias `−P`, `3` = output with
the edges `1 → 3` of gain `+D` and `2 → 3` of gain `−D` and nothing else. Without one: vertices
`0`, `1` = the two hinges and `2` = output. So the output is
`D(ρ(S(x) − (P − w)) − ρ(S(x) − P))` with `S(x) = a·u(x) + ∑_j b_j x_j`. -/
def toNet (C : CommonRamp c) : Net (Coord c) (Occ c) :=
  match C.share with
  | some (o₁, o₂) =>
    { h := 3
      occ := fun p => match p with
        | .inEdge t i =>
          if i.val = 0 then C.wireIn t
          else if i.val = 1 then (C.direct t).map Prod.fst
          else if i.val = 2 then (C.direct t).map Prod.snd
          else none
        | .hidEdge i j =>
          if i.val = 1 ∧ j.val = 0 then some o₁
          else if i.val = 2 ∧ j.val = 0 then some o₂
          else if i.val = 3 ∧ j.val = 1 then some .gainPos
          else if i.val = 3 ∧ j.val = 2 then some .gainNeg
          else none
        | .bias i =>
          if i.val = 0 then C.wireBias
          else if i.val = 1 then some .biasHi
          else if i.val = 2 then some .biasLo
          else none }
  | none =>
    { h := 2
      occ := fun p => match p with
        | .inEdge t i =>
          if i.val = 0 then (C.direct t).map Prod.fst
          else if i.val = 1 then (C.direct t).map Prod.snd
          else none
        | .hidEdge i j =>
          if i.val = 2 ∧ j.val = 0 then some .gainPos
          else if i.val = 2 ∧ j.val = 1 then some .gainNeg
          else none
        | .bias i =>
          if i.val = 0 then some .biasHi
          else if i.val = 1 then some .biasLo
          else none }

/-- **Legal common ramp** (Lemma 4.9's conventions, at-most-once rule): its network is permitted
with cap four; every used sharing, direct and wire occurrence has a positive value (a single
positive inventory primitive); the two sharing occurrences have identical values, and so do the
two direct occurrences of every input; and when there is no sharing edge the wire is omitted
(no wire parameters). -/
def Legal (C : CommonRamp c) : Prop :=
  C.toNet.Permitted InventoryRule.atMostOnce 4 ∧
  (∀ o₁ o₂, C.share = some (o₁, o₂) → 0 < c.inv o₁ ∧ c.inv o₁ = c.inv o₂) ∧
  (∀ t o₁ o₂, C.direct t = some (o₁, o₂) → 0 < c.inv o₁ ∧ c.inv o₁ = c.inv o₂) ∧
  (∀ o, C.wireBias = some o → 0 < c.inv o) ∧
  (∀ t o, C.wireIn t = some o → 0 < c.inv o) ∧
  (C.share = none → C.wireBias = none ∧ ∀ t, C.wireIn t = none)

end CommonRamp

end ReLUSynth.Boolean


