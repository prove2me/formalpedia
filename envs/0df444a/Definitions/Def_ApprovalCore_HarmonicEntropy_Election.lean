-- Prove2me | Definitions.Def_ApprovalCore_HarmonicEntropy_Election
-- name    : ApprovalCore_HarmonicEntropy_Election
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T07:30:36.938798+00:00
-- url     : https://prove2.me/theorems/6872816c-65a2-4455-97a7-3fae40213614
-- title:
--   Approval-based committee elections, the core and core+ at a quota $q$, payment systems and $P_X(W)$
-- statement:
--   An **approval-based committee election** $I = (A, k)$ has voters $N = [n]$, a finite set of candidates $C = \{c_1, \dots, c_m\}$, an approval set $A_i \subseteq C$ for each voter (arbitrary, possibly empty) and a committee size $k$ with $1 \le k \le m-1$. A **committee** is a set $W \subseteq C$; $\mathcal W$ is the set of committees of size at most $k$ and $\mathcal W_k$ those of size exactly $k$. Voter $i$'s utility is $u_i(W) = |A_i \cap W|$ and $N_c = \{i \in N : c \in A_i\}$. A **quota** $q$ is a real number.
--
--   **Core (eq. (1)).** A non-empty coalition $S \subseteq N$ **blocks** $W$ if there is $T \subseteq C$ with $|S| \ge q\,|T|$ and $u_i(T) \ge u_i(W) + 1$ for every $i \in S$. A committee $W \in \mathcal W$ is **in the core** if no non-empty coalition blocks it.
--
--   **Core+ (Definition 3.1).** A **fractional blocking coalition** for $W$ is $y \in \mathbb R^n_{\ge 0} \setminus \{0\}$ and $z \in \mathbb R^m_{\ge 0}$ (indexed by all candidates) with $\sum_{i} y_i \ge q \sum_{c} z_c$ and, for every voter $i \in N$,
--   $$\sum_{c \in A_i \setminus W} z_c + \sum_{c \in A_i \cap W} \min\{y_i, z_c\} \ \ge\ (u_i(W) + 1)\, y_i. \qquad (2)$$
--   A committee $W \in \mathcal W$ **satisfies core+** if it admits no fractional blocking coalition.
--
--   **Payment systems.** For a committee $W$, a payment system $(r, p)$ gives each voter a reserve $r_i \in [0,1]$ and a payment $p_{ic} \in [0,1]$ to each approved winner $c \in A_i \cap W$ (no payments to other candidates). The conditions are
--   (P1) $r_i + \sum_{c \in A_i \cap W} p_{ic} = 1$ for each $i$;
--   (P2) $r_i \ge p_{ic}$ for each $i$ and $c \in A_i \cap W$;
--   (P3) $\sum_{i \in N_c} r_i < q$ for each $c \in C \setminus W$;
--   (P4) $\sum_{i \in N_c} p_{ic} \le q$ for each $c \in W$.
--   $P_X(W)$ is the set of payment systems satisfying (P$x$) for every $x \in X$; the mission uses $P_{1234}$, $P_{124}$ and $P_{14}$.
--
--   **Formalization Note.** Voters are `Fin n` and candidates `Fin m` (0-based); `Instance n m` carries $A$, $k$ and the constraints $1 \le k$, $k + 1 \le m$. `InCore I q W` and `SatisfiesCorePlus I q W` include $|W| \le k$ (membership in $\mathcal W$). A payment system is a pair `(r, p)` with `p : Fin n → Fin m → ℝ`; `IsPaymentSystem` imposes $r_i, p_{ic} \in [0,1]$ on approved winners and $p_{ic} = 0$ for every $c \notin A_i \cap W$, so no stray payment enters (P4). Payments sets are subsets of $\mathbb R^n \times \mathbb R^{n \times m}$ with the product topology.
-- source:
--   Becker, Greger, Peters, Existence of the Core in Approval-Based Committee Elections, STOC 2027 submission (manuscript sha256 7cc237dc…), §2 p. 4; §3 p. 4 (eq. (1), Definition 3.1, eq. (2)); §3 p. 5 ((P1)–(P4), P_X(W))

import Mathlib

namespace ApprovalCore.HarmonicEntropy

/-!
# Approval-based committee elections, the core, core+ and payment systems

Becker, Greger, Peters, *Existence of the Core in Approval-Based Committee Elections*,
STOC 2027 submission (manuscript sha256 7cc237dc…), §2 p. 4 (instances, utility, `N_c`,
`W`, `W_k`, quota), §3 p. 4 (core, eq. (1); core+, Definition 3.1, eq. (2)), §3 p. 5
(payment systems, (P1)–(P4), `P_X(W)`).

Voters are `Fin n` (`N = [n]`), candidates are `Fin m` (`C = {c₁, …, c_m}`), both 0-based.
A committee is a `Finset (Fin m)`.
-/

/-- An approval-based committee election instance `I = (A, k)` (p. 4): `n` voters, `m`
candidates, an approval profile `A i ⊆ C` (arbitrary, possibly empty), and a committee
size `k ∈ [m − 1]`, i.e. `1 ≤ k` and `k + 1 ≤ m`. -/
structure Instance (n m : ℕ) where
  /-- The approval set `A_i` of voter `i`. -/
  A : Fin n → Finset (Fin m)
  /-- The committee size. -/
  k : ℕ
  one_le_k : 1 ≤ k
  k_succ_le_m : k + 1 ≤ m

variable {n m : ℕ}

/-- Utility `u_i(W) = |A_i ∩ W|` (p. 4). -/
def utility (A : Fin n → Finset (Fin m)) (i : Fin n) (W : Finset (Fin m)) : ℕ :=
  (A i ∩ W).card

/-- `N_c = {i ∈ N : c ∈ A_i}`, the voters approving `c` (p. 4). -/
def supporters (A : Fin n → Finset (Fin m)) (c : Fin m) : Finset (Fin n) :=
  Finset.univ.filter (fun i => c ∈ A i)

/-- A non-empty coalition `S` blocks `W` at quota `q` (p. 4, eq. (1)): there is a proposal
`T ⊆ C` with `|S| ≥ q · |T|` and `u_i(T) ≥ u_i(W) + 1` for every `i ∈ S`. -/
def Blocks (A : Fin n → Finset (Fin m)) (q : ℝ) (W : Finset (Fin m))
    (S : Finset (Fin n)) : Prop :=
  S.Nonempty ∧ ∃ T : Finset (Fin m), (S.card : ℝ) ≥ q * (T.card : ℝ) ∧
    ∀ i ∈ S, utility A i T ≥ utility A i W + 1

/-- `W` is in the core at quota `q` (p. 4): `W ∈ W` (i.e. `|W| ≤ k`) and no non-empty
coalition blocks `W`. -/
def InCore (I : Instance n m) (q : ℝ) (W : Finset (Fin m)) : Prop :=
  W.card ≤ I.k ∧ ∀ S : Finset (Fin n), ¬ Blocks I.A q W S

/-- A fractional blocking coalition for `W` at quota `q` (Definition 3.1, p. 4):
`y ∈ ℝⁿ_{≥0} \ {0}`, `z ∈ ℝᵐ_{≥0}` (indexed by all candidates, winners and losers) with
`∑_i y_i ≥ q ∑_c z_c` and, for every voter `i`,
`∑_{c ∈ A_i \ W} z_c + ∑_{c ∈ A_i ∩ W} min{y_i, z_c} ≥ (u_i(W) + 1) y_i` (eq. (2)). -/
def IsFractionalBlockingCoalition (A : Fin n → Finset (Fin m)) (q : ℝ)
    (W : Finset (Fin m)) (y : Fin n → ℝ) (z : Fin m → ℝ) : Prop :=
  (∀ i, 0 ≤ y i) ∧ y ≠ 0 ∧ (∀ c, 0 ≤ z c) ∧
    (∑ i, y i ≥ q * ∑ c, z c) ∧
    ∀ i, (∑ c ∈ A i \ W, z c) + (∑ c ∈ A i ∩ W, min (y i) (z c))
      ≥ ((utility A i W : ℝ) + 1) * y i

/-- `W` satisfies core+ at quota `q` (Definition 3.1, p. 4): `W ∈ W` (i.e. `|W| ≤ k`) and
`W` admits no fractional blocking coalition. -/
def SatisfiesCorePlus (I : Instance n m) (q : ℝ) (W : Finset (Fin m)) : Prop :=
  W.card ≤ I.k ∧ ∀ y z, ¬ IsFractionalBlockingCoalition I.A q W y z

/-- A pair `(r, p)` of reserves `r_i` and payments `p_{ic}`. Payments are functions on all
pairs `(i, c)`; `IsPaymentSystem` forces `p_{ic} = 0` unless `c ∈ A_i ∩ W`. -/
abbrev PaymentPair (n m : ℕ) := (Fin n → ℝ) × (Fin n → Fin m → ℝ)

/-- `(r, p)` is a payment system for `W` (p. 5): `r_i ∈ [0, 1]` for every voter, a payment
`p_{ic} ∈ [0, 1]` for each approved winner `c ∈ A_i ∩ W`, and no payment to any other
candidate (`p_{ic} = 0` for `c ∉ A_i ∩ W`). -/
def IsPaymentSystem (A : Fin n → Finset (Fin m)) (W : Finset (Fin m))
    (rp : PaymentPair n m) : Prop :=
  (∀ i, rp.1 i ∈ Set.Icc (0 : ℝ) 1) ∧
    (∀ i, ∀ c ∈ A i ∩ W, rp.2 i c ∈ Set.Icc (0 : ℝ) 1) ∧
    (∀ i c, c ∉ A i ∩ W → rp.2 i c = 0)

/-- (P1): `r_i + ∑_{c ∈ A_i ∩ W} p_{ic} = 1` for each voter (p. 5). -/
def P1 (A : Fin n → Finset (Fin m)) (W : Finset (Fin m)) (rp : PaymentPair n m) : Prop :=
  ∀ i, rp.1 i + ∑ c ∈ A i ∩ W, rp.2 i c = 1

/-- (P2): `r_i ≥ p_{ic}` for each voter and each `c ∈ A_i ∩ W` (p. 5). -/
def P2 (A : Fin n → Finset (Fin m)) (W : Finset (Fin m)) (rp : PaymentPair n m) : Prop :=
  ∀ i, ∀ c ∈ A i ∩ W, rp.1 i ≥ rp.2 i c

/-- (P3): `∑_{i ∈ N_c} r_i < q` for each `c ∈ C \ W` (p. 5). -/
def P3 (A : Fin n → Finset (Fin m)) (q : ℝ) (W : Finset (Fin m))
    (rp : PaymentPair n m) : Prop :=
  ∀ c, c ∉ W → ∑ i ∈ supporters A c, rp.1 i < q

/-- (P4): `∑_{i ∈ N_c} p_{ic} ≤ q` for each `c ∈ W` (p. 5). -/
def P4 (A : Fin n → Finset (Fin m)) (q : ℝ) (W : Finset (Fin m))
    (rp : PaymentPair n m) : Prop :=
  ∀ c ∈ W, ∑ i ∈ supporters A c, rp.2 i c ≤ q

/-- `P1234(W)`: payment systems for `W` satisfying (P1)–(P4) (p. 5). -/
def P1234 (A : Fin n → Finset (Fin m)) (q : ℝ) (W : Finset (Fin m)) :
    Set (PaymentPair n m) :=
  {rp | IsPaymentSystem A W rp ∧ P1 A W rp ∧ P2 A W rp ∧ P3 A q W rp ∧ P4 A q W rp}

/-- `P124(W)`: payment systems for `W` satisfying (P1), (P2), (P4) (p. 5). -/
def P124 (A : Fin n → Finset (Fin m)) (q : ℝ) (W : Finset (Fin m)) :
    Set (PaymentPair n m) :=
  {rp | IsPaymentSystem A W rp ∧ P1 A W rp ∧ P2 A W rp ∧ P4 A q W rp}

/-- `P14(W)`: payment systems for `W` satisfying (P1) and (P4) (p. 5). -/
def P14 (A : Fin n → Finset (Fin m)) (q : ℝ) (W : Finset (Fin m)) :
    Set (PaymentPair n m) :=
  {rp | IsPaymentSystem A W rp ∧ P1 A W rp ∧ P4 A q W rp}

end ApprovalCore.HarmonicEntropy


