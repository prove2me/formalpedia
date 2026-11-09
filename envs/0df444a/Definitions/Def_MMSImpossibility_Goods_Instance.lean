-- Prove2me | Definitions.Def_MMSImpossibility_Goods_Instance
-- name    : MMSImpossibility_Goods_Instance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:13:54.528181+00:00
-- url     : https://prove2.me/theorems/4e1c9dfd-c0ff-4a76-a747-fa87982adf4a
-- title:
--   §2.1 — the instance: goods, auxiliary weights, corrections and valuations
-- statement:
--   Let $n \ge 2^{16}$ and $k = 8\lceil\log_2 n\rceil$. Set $x_j = k(6k+j)$, $H = 17k^2$, $T = 4kH = 68k^3$, $U = 7k^3 - k^2/2$. The $m = n+5k$ goods and their **auxiliary weights** $w$ are
--
--   | good | indices | $w(g)$ |
--   |---|---|---|
--   | $Z_j$ | $0\le j<2k$ | $T-H$ |
--   | $X_j$ | $0\le j<2k$ | $x_j$ |
--   | $Y_j$ | $0\le j<2k$ | $H-x_j$ |
--   | $G_h$ | $0\le h<k$ | $H$ |
--   | $P$ | 1 | $T-U$ |
--   | $Q$ | 1 | $T-kH+U$ |
--   | $D_t$ | $1\le t\le n-2k-2$ | $T$ |
--
--   For a type (label set) $S$ the **correction** is $\rho_S(X_j) = -\mathbf 1[j\notin S]$, $\rho_S(Y_j) = \mathbf 1[j\in S]$, $\rho_S(Z_j)=1$, $\rho_S(G_h)=-1$, $\rho_S(P)=0$, $\rho_S(Q)=-k$, $\rho_S(D_t)=0$, and the valuation of an agent of type $S$ is
--
--   $$v_S(g) = 3w(g) + \rho_S(g), \qquad v_S(B) = 3w(B) + \rho_S(B) \quad (3)$$
--
--   extended additively. Agent $i$ has the type $S(\sigma_i)$ of a word $\sigma_i$. Also $\mu = 3T$ and $\ell = k/24$. The goods $Z_j, P, Q, D_t$ are **high**, the goods $X_j, Y_j, G_h$ are **low**. For the proof of Proposition 8 the following sets are named: $g = |\{h : G_h\in B_P\cup B_Q\}|$, $F = \{j : X_j, Y_j \in B_P\cup B_Q\}$, $I_Q = \{j\in S_Q : Y_j\in B_Q\}$, $d = k-|I_Q|$, and $R = \{j\in S_Q : X_j \in B_P\}$.
--
--   This is the instance that witnesses Theorem 1.
--
--   **Formalization Note** The items are `Fin (n + 5k)`, decoded by index ranges: $0..2k-1 \mapsto Z_j$, $2k..4k-1\mapsto X_j$, $4k..6k-1\mapsto Y_j$, $6k..7k-1\mapsto G_h$, $7k\mapsto P$, $7k+1\mapsto Q$, and $7k+2+t \mapsto D_{t+1}$; for $n \ge 2k+2$ this is a bijection onto the paper's goods. Weights and values are real numbers; $U$ is computed in $\mathbb R$ (it is an integer since $k$ is even).
-- source:
--   Ezra and Garbuz, Improved Impossibility Bounds for Maximin Share Allocations, 2026 preprint, STOC 2027 submission #115, SHA-256 8e8d63bbe3b0c850c561528c6e8d5bdb6da3bc426e5f64316cc948d5a31d64a6, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/115.pdf, §2.1 Description of the Instance, PDF pp. 7–8 (printed pp. 6–7), equation (3); named sets from the proof of Proposition 8, PDF pp. 10–11

import Mathlib
import Definitions.Def_MMSImpossibility_Goods_Setting
import Definitions.Def_MMSImpossibility_Goods_Code

namespace MMSImpossibility.Goods

/-- §2.1 (PDF p. 7): the code length `k = 8⌈log₂ n⌉`; for `n ≥ 1`, `Nat.clog 2 n = ⌈log₂ n⌉`. -/
def kOf (n : ℕ) : ℕ := 8 * Nat.clog 2 n

/-- §2.1 (PDF p. 8): the goods of the instance, by family. `Z j`, `X j`, `Y j` for
`0 ≤ j < 2k`, `G h` for `0 ≤ h < k`, the single goods `P` and `Q`, and `D t`, which is the
paper's `D_{t+1}` (the paper indexes `D_t` by `1 ≤ t ≤ n - 2k - 2`; here `t` starts at `0`). -/
inductive Good (k : ℕ) where
  | Z : Fin (2 * k) → Good k
  | X : Fin (2 * k) → Good k
  | Y : Fin (2 * k) → Good k
  | G : Fin k → Good k
  | P : Good k
  | Q : Good k
  | D : ℕ → Good k
  deriving DecidableEq

/-- §2.1 (PDF p. 7–8): the `m = n + 5k` items, listed by index ranges:
`0 … 2k-1 ↦ Z_j`, `2k … 4k-1 ↦ X_j`, `4k … 6k-1 ↦ Y_j`, `6k … 7k-1 ↦ G_h`, `7k ↦ P`,
`7k+1 ↦ Q`, and `7k+2+t ↦ D_{t+1}` for `0 ≤ t < n - 2k - 2`. For `n ≥ 2k + 2` this is a
bijection from `Fin (n + 5k)` onto the paper's item set. -/
def decode (n k : ℕ) (i : Fin (n + 5 * k)) : Good k :=
  if h1 : i.val < 2 * k then .Z ⟨i.val, h1⟩
  else if h2 : i.val < 4 * k then .X ⟨i.val - 2 * k, by omega⟩
  else if h3 : i.val < 6 * k then .Y ⟨i.val - 4 * k, by omega⟩
  else if h4 : i.val < 7 * k then .G ⟨i.val - 6 * k, by omega⟩
  else if i.val = 7 * k then .P
  else if i.val = 7 * k + 1 then .Q
  else .D (i.val - (7 * k + 2))

/-- High goods (PDF p. 9): `Z_j`, `P`, `Q`, `D_t`. -/
def IsHigh {k : ℕ} : Good k → Prop
  | .Z _ => True
  | .P => True
  | .Q => True
  | .D _ => True
  | _ => False

instance {k : ℕ} : DecidablePred (IsHigh (k := k)) := fun g => by
  cases g <;> simp only [IsHigh] <;> infer_instance

/-- Low goods (PDF p. 9): the goods of type `X`, `Y` or `G`. -/
def IsLow {k : ℕ} (g : Good k) : Prop := ¬ IsHigh g

instance {k : ℕ} : DecidablePred (IsLow (k := k)) := fun g => by
  unfold IsLow; infer_instance

/-- §2.1 (PDF p. 8): `x_j = k(6k + j)`. -/
def xw (k : ℕ) (j : Fin (2 * k)) : ℝ := (k : ℝ) * (6 * (k : ℝ) + (j : ℝ))

/-- §2.1 (PDF p. 8): `H = 17k²`. -/
def Hw (k : ℕ) : ℝ := 17 * (k : ℝ) ^ 2

/-- §2.1 (PDF p. 8): `T = 4kH` (`= 68k³`). -/
def Tw (k : ℕ) : ℝ := 4 * (k : ℝ) * Hw k

/-- §2.1 (PDF p. 8): `U = 7k³ - k²/2`. -/
noncomputable def Uw (k : ℕ) : ℝ := 7 * (k : ℝ) ^ 3 - (k : ℝ) ^ 2 / 2

/-- §2.1 (PDF p. 8, table): the auxiliary weight `w(g)`. -/
noncomputable def weight {k : ℕ} : Good k → ℝ
  | .Z _ => Tw k - Hw k
  | .X j => xw k j
  | .Y j => Hw k - xw k j
  | .G _ => Hw k
  | .P => Tw k - Uw k
  | .Q => Tw k - (k : ℝ) * Hw k + Uw k
  | .D _ => Tw k

/-- §2.1 (PDF p. 8): the correction function `ρ_S` of a type (label set) `S`:
`ρ_S(X_j) = -1[j ∉ S]`, `ρ_S(Y_j) = 1[j ∈ S]`, `ρ_S(Z_j) = 1`, `ρ_S(G_h) = -1`,
`ρ_S(P) = 0`, `ρ_S(Q) = -k`, `ρ_S(D_t) = 0`. -/
def corr {k : ℕ} (S : Finset (Fin (2 * k))) : Good k → ℝ
  | .X j => if j ∈ S then 0 else -1
  | .Y j => if j ∈ S then 1 else 0
  | .Z _ => 1
  | .G _ => -1
  | .P => 0
  | .Q => -(k : ℝ)
  | .D _ => 0

/-- Equation (3), PDF p. 8: `v_S(g) = 3w(g) + ρ_S(g)`. -/
noncomputable def itemValue {k : ℕ} (S : Finset (Fin (2 * k))) (g : Good k) : ℝ :=
  3 * weight g + corr S g

/-- `w(B) = ∑_{g ∈ B} w(g)` for a set `B` of items (PDF p. 8). -/
noncomputable def weightB {n k : ℕ} (B : Finset (Fin (n + 5 * k))) : ℝ :=
  ∑ g ∈ B, weight (decode n k g)

/-- `ρ_S(B) = ∑_{g ∈ B} ρ_S(g)` for a set `B` of items (PDF p. 8). -/
def corrB {n k : ℕ} (S : Finset (Fin (2 * k))) (B : Finset (Fin (n + 5 * k))) : ℝ :=
  ∑ g ∈ B, corr S (decode n k g)

/-- The additive valuation of the instance (PDF p. 8): agent `i` has type
`S_i = S(σ i)`, the label set of her codeword `σ i`, and values a bundle `B` at
`v_{S_i}(B) = ∑_{g ∈ B} (3w(g) + ρ_{S_i}(g))`. The items are `Fin (n + 5k)` with
`k = kOf n`. -/
noncomputable def valuation (n : ℕ) (σ : Fin n → (Fin (kOf n) → Fin 2)) :
    Fin n → Finset (Fin (n + 5 * kOf n)) → ℝ :=
  fun i B => ∑ g ∈ B, itemValue (labelSet (σ i)) (decode n (kOf n) g)

/-- `µ = 3T` (PDF p. 8), the proportional share of every agent. -/
def mu (k : ℕ) : ℝ := 3 * Tw k

/-- `ℓ = k/24` (PDF p. 9), a real number. -/
noncomputable def ell (k : ℕ) : ℝ := (k : ℝ) / 24

/-- A set of items contains the good `x` (some index of it decodes to `x`). -/
def Contains {n k : ℕ} (B : Finset (Fin (n + 5 * k))) (x : Good k) : Prop :=
  ∃ g ∈ B, decode n k g = x

instance {n k : ℕ} (B : Finset (Fin (n + 5 * k))) (x : Good k) : Decidable (Contains B x) := by
  unfold Contains; infer_instance

/-- PDF p. 9: the number of high goods in a set of items. -/
def highCount {n k : ℕ} (B : Finset (Fin (n + 5 * k))) : ℕ :=
  (B.filter (fun g => IsHigh (decode n k g))).card

/-- PDF p. 10: `g = |{h : G_h ∈ B_P ∪ B_Q}|`. -/
def gCount {n k : ℕ} (BP BQ : Finset (Fin (n + 5 * k))) : ℕ :=
  (Finset.univ.filter (fun h : Fin k => Contains (BP ∪ BQ) (.G h))).card

/-- PDF p. 10: `F = {j ∈ {0,…,2k-1} : X_j, Y_j ∈ B_P ∪ B_Q}`. -/
def Fset {n k : ℕ} (BP BQ : Finset (Fin (n + 5 * k))) : Finset (Fin (2 * k)) :=
  Finset.univ.filter (fun j => Contains (BP ∪ BQ) (.X j) ∧ Contains (BP ∪ BQ) (.Y j))

/-- PDF p. 10: `I_Q = {j ∈ S_Q : Y_j ∈ B_Q}`. -/
def IQ {n k : ℕ} (SQ : Finset (Fin (2 * k))) (BQ : Finset (Fin (n + 5 * k))) :
    Finset (Fin (2 * k)) :=
  SQ.filter (fun j => Contains BQ (.Y j))

/-- PDF p. 10: `d = k - |I_Q|`. -/
def dCount {n k : ℕ} (SQ : Finset (Fin (2 * k))) (BQ : Finset (Fin (n + 5 * k))) : ℕ :=
  k - (IQ SQ BQ).card

/-- PDF p. 11: `{j : X_j ∈ B}`. -/
def xLabels {n k : ℕ} (B : Finset (Fin (n + 5 * k))) : Finset (Fin (2 * k)) :=
  Finset.univ.filter (fun j => Contains B (.X j))

/-- PDF p. 11: `R = {j ∈ S_Q : X_j ∈ B_P}`. -/
def Rset {n k : ℕ} (SQ : Finset (Fin (2 * k))) (BP : Finset (Fin (n + 5 * k))) :
    Finset (Fin (2 * k)) :=
  SQ.filter (fun j => Contains BP (.X j))

end MMSImpossibility.Goods


