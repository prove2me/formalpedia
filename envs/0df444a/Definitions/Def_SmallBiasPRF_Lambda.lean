-- Prove2me | Definitions.Def_SmallBiasPRF_Lambda
-- name    : SmallBiasPRF_Lambda
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:09:40.264407+00:00
-- url     : https://prove2.me/theorems/2f1b03f3-6748-4603-8bf1-07866a1e0d50
-- title:
--   The contraction factor $\Lambda_B(S)$, the counts $C_{B,r}(S)$ and noncontracting states
-- statement:
--   For a finite set $B$ and a (partial) state $S:B\to\mathbb F_3$, the **contraction factor** is
--
--   $$\Lambda_B(S)=\mathop{\mathbb E}_{\rho\in\mathbb F_3}\Big[\prod_{a\in B}(-1)^{S(a)+\rho\bmod 3}\Big],$$
--
--   where $S(a)+\rho \bmod 3$ is identified with its canonical integer representative in $\{0,1,2\}$, and $\Lambda_\emptyset(\emptyset)=1$. For $r\in\mathbb F_3$ the **counting function** is $C_{B,r}(S)=|\{a\in B:S(a)=r\}|$, and $S$ is **noncontracting** when
--
--   $$C_{B,0}(S)\bmod 2=C_{B,1}(S)\bmod 2=C_{B,2}(S)\bmod 2,$$
--
--   condition (14), and **contracting** otherwise. Lemma 11 writes the bias of the single-bit construction as a product of the factors $|\Lambda_{A_j}|$, and Lemma 17 shows $|\Lambda_B(S)|\in\{1,1/3\}$ according to whether $S$ is noncontracting.
--
--   **Formalization Note** The state is a total function $S:\alpha\to$ `ZMod 3` read only on $B$ (the paper's $S|_B$); the representative is `(S a + ρ).val`. For $B=\emptyset$ the formula already gives $1$.
-- source:
--   Dinur–Ishai, Towards Asymptotically Optimal Pseudorandom Functions: Linear-Size Circuits with Exponentially Small Bias, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), §5.2, display (7), p.19 (PDF 22); §5.5, display (14), p.24 (PDF 27)

import Mathlib

namespace SmallBiasPRF

/-- The **contraction factor** of display (7), p.19 (PDF p.22): for a finite set `B` and a (partial)
state `S : B → 𝔽₃`,
`Λ_B(S) = E_{ρ∈𝔽₃}[∏_{a∈B} (−1)^{S(a)+ρ mod 3}]`,
where `S(a) + ρ mod 3` is identified with its canonical integer representative in `{0, 1, 2}`;
`Λ_∅(∅) = 1`.
Dinur–Ishai, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), (7), p.19 (PDF p.22).

**Formalization Note.** The state is a total function `S : α → ZMod 3` of which only the values on
`B` are read (this is `Λ_B(S|_B)` in the paper's notation). The representative is `(S a + ρ).val`.
For `B = ∅` the formula gives `1`, the paper's convention `Λ_∅(∅) = 1`. -/
noncomputable def Lambda {α : Type*} (B : Finset α) (S : α → ZMod 3) : ℝ :=
  (1 / 3 : ℝ) * ∑ ρ : ZMod 3, ∏ a ∈ B, (-1 : ℝ) ^ (S a + ρ).val

/-- The counting function `C_{B,r}(S) = |{a ∈ B : S(a) = r}|` (§5.5, p.24 (PDF p.27)).
Dinur–Ishai, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), §5.5, p.24. -/
def countVal {α : Type*} (B : Finset α) (S : α → ZMod 3) (r : ZMod 3) : ℕ :=
  (B.filter fun a => S a = r).card

/-- A state `S : B → 𝔽₃` is **noncontracting** when the three count parities agree, condition (14),
p.24 (PDF p.27): `C_{B,0}(S) mod 2 = C_{B,1}(S) mod 2 = C_{B,2}(S) mod 2`; otherwise it is
contracting.
Dinur–Ishai, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), (14), p.24. -/
def IsNoncontracting {α : Type*} (B : Finset α) (S : α → ZMod 3) : Prop :=
  countVal B S 0 % 2 = countVal B S 1 % 2 ∧ countVal B S 1 % 2 = countVal B S 2 % 2

end SmallBiasPRF


