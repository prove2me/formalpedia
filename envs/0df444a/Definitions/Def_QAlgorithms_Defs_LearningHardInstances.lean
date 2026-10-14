-- Prove2me | Definitions.Def_QAlgorithms_Defs_LearningHardInstances
-- name    : QAlgorithms_Defs_LearningHardInstances
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-13T17:54:18.313545+00:00
-- url     : https://prove2.me/theorems/c650a2c9-8637-46c0-9b7c-43bb43a7181f
-- title:
--   The hard instances of the PGM lower bounds (shared definition layer)
-- statement:
--   The hard instances of the PGM lower bounds (shared definition layer)
--
--   ### QAlgorithms.Learning.codeConcept
--
--   This defines a Boolean function $c_{M,x}$ on $\{0,\dots,d-1\}$. Its inputs are:
--
--   - natural numbers $d, k$;
--   - a $d\times k$ matrix $M$ over the field $\mathbb{F}_2$;
--   - a vector $x \in \mathbb{F}_2^k$.
--
--   The function is
--   $$c_{M,x}(i) = \begin{cases}\mathsf{true} & \text{if } (Mx)_i = 1,\\ \mathsf{false} & \text{otherwise,}\end{cases}$$
--   where $(Mx)_i = \sum_{j<k} M_{ij}x_j \bmod 2$. Equivalently, $c_{M,x}$ is the codeword $Mx \in \mathbb{F}_2^d$ read as a bit string, with $1 \mapsto \mathsf{true}$ and $0 \mapsto \mathsf{false}$.
--
--   Edge cases follow directly from the formula:
--
--   - If $d=0$, the function has empty domain.
--   - If $k=0$, then $Mx=0$, so $c_{M,x}$ is constantly $\mathsf{false}$.
--
--   ### QAlgorithms.Learning.pacHardConcept
--
--   This defines a Boolean function $\tilde c_{M,x}$ on $\{0,1,\dots,d\}$, which has $d+1$ points. Its inputs are natural numbers $d,k$, a $d\times k$ matrix $M$ over $\mathbb{F}_2$, and $x\in\mathbb{F}_2^k$. It prepends a constant $\mathsf{false}$ coordinate to the codeword function:
--   $$\tilde c_{M,x}(0) = \mathsf{false}, \qquad \tilde c_{M,x}(i+1) = c_{M,x}(i) \quad (0 \le i < d).$$
--
--   Here $c_{M,x}(i)$ is $\mathsf{true}$ exactly when $(Mx)_i = 1$ in $\mathbb{F}_2$. When $d=0$, $\tilde c_{M,x}$ is the single-point function with value $\mathsf{false}$.
--
--   ### QAlgorithms.Learning.pacHardDist
--
--   This defines a real-valued function $D_{d,\varepsilon}$ on $\{0,1,\dots,d\}$, for a natural number $d$ and a real number $\varepsilon$:
--   $$D_{d,\varepsilon}(0) = 1 - 20\varepsilon, \qquad D_{d,\varepsilon}(i+1) = \frac{20\varepsilon}{d} \quad (0\le i<d).$$
--
--   Nothing about $\varepsilon$ is assumed, so the following properties depend on its value:
--
--   - **Sum.** For $d \ge 1$ the values sum to $1$.
--   - **Nonnegativity.** All values are nonnegative only when $0 \le \varepsilon \le 1/20$. For other $\varepsilon$, some values are negative.
--   - **The case $d=0$.** The domain is the single point $0$ and the only value is $1-20\varepsilon$, so the values sum to $1$ only if $\varepsilon = 0$. The division by $d = 0$ never actually occurs, since there are no points $i+1$.
--
--   ### QAlgorithms.Learning.agnHardDist
--
--   This defines a real-valued function $\mathcal{D}_{M,\varepsilon,x}$ on pairs $(i,b)$ with $i\in\{0,\dots,d-1\}$ and $b \in\{\mathsf{true},\mathsf{false}\}$. Its inputs are natural numbers $d,k$, a $d\times k$ matrix $M$ over $\mathbb{F}_2$, a real number $\varepsilon$, and $x\in\mathbb{F}_2^k$:
--   $$\mathcal{D}_{M,\varepsilon,x}(i,b) = \begin{cases} \dfrac{1+10\varepsilon}{2d} & \text{if } b = c_{M,x}(i),\\[2mm] \dfrac{1-10\varepsilon}{2d} & \text{otherwise,}\end{cases}$$
--   where $c_{M,x}(i)$ is $\mathsf{true}$ exactly when $(Mx)_i = 1$ in $\mathbb{F}_2$.
--
--   So each point $i$ splits its total mass $1/d$ between its two labels. The label that agrees with the codeword gets $(1+10\varepsilon)/(2d)$ and the other gets $(1-10\varepsilon)/(2d)$.
--
--   As with the previous definition, $\varepsilon$ is unconstrained:
--
--   - **Sum.** For $d\ge 1$ the values sum to $1$.
--   - **Nonnegativity.** All values are nonnegative only when $|\varepsilon|\le 1/10$. For $\varepsilon<0$, the label that disagrees with the codeword is the heavier one.
--   - **The case $d=0$.** The domain is empty, so the function has no values and the division by zero is never evaluated.
-- source:
--   https://github.com/shiy1022/lean-quantum-complexity/blob/main/algorithms/QAlgorithms/Defs/LearningHardInstances.lean . Exact primary-source page locators are preserved in the declaration docstrings.

import Definitions.Def_QAlgorithms_Defs_Learning
/-!
# The hard instances of the PGM lower bounds (shared definition layer)

S. Arunachalam, *Quantum Algorithms and Learning Theory* (PhD thesis, 2018), §7.5–7.6, cited
"Arunachalam p.N" (PDF pages). A linear code has generator matrix `M ∈ F₂^{d×k}`
(`Matrix (Fin d) (Fin k) (ZMod 2)`) and codewords `Mx`, `x ∈ {0,1}^k`. The shattered set is
represented by its labels: `{s_0, …, s_d}` is `Fin (d + 1)` (`s_0` is `0`, `s_i` is `i` for
`i ∈ [d]`), and `{s_1, …, s_d}` is `Fin d` (`s_i` is `i − 1`).
-/

namespace QAlgorithms.Learning

/-- Arunachalam p.176 (proof of Thm 7.5.6) and p.182 (§7.6.2): the codeword `Mx` read as a
Boolean function on `[d]`, `i ↦ ((Mx)_i = 1)`. -/
def codeConcept {d k : ℕ} (M : Matrix (Fin d) (Fin k) (ZMod 2)) (x : Fin k → ZMod 2) :
    Fin d → Bool :=
  fun i => decide ((M.mulVec x) i = 1)

/-- Arunachalam p.176 (proof of Thm 7.5.6): the concept `c^x` on the shattered set
`{s_0, …, s_d}`, with `c^x(s_0) = 0` and `c^x(s_i) = (Mx)_i` for `i ∈ [d]`. -/
def pacHardConcept {d k : ℕ} (M : Matrix (Fin d) (Fin k) (ZMod 2)) (x : Fin k → ZMod 2) :
    Fin (d + 1) → Bool :=
  Fin.cons false (codeConcept M x)

/-- Arunachalam p.175 (proof of Thm 7.5.6): the distribution `D(s_0) = 1 − 20ε`,
`D(s_i) = 20ε/d` for `i ∈ [d]`. The state `|ψ_x⟩` of Lemma 7.5.7 is
`exampleState (pacHardConcept M x) (pacHardDist d ε)`. -/
noncomputable def pacHardDist (d : ℕ) (ε : ℝ) : Fin (d + 1) → ℝ :=
  Fin.cons (1 - 20 * ε) fun _ => 20 * ε / (d : ℝ)

/-- Arunachalam p.178 (proof of Thm 7.5.8) and p.179 (Lemma 7.5.9): the distribution
`D_x(s_i, b) = (1/d)(1/2 + (1/2)(−1)^{(Mx)_i + b} α)` on `[d] × {0,1}`, with `α = 10ε`, the value
with which the proof of Lemma 7.5.9 computes (`√(D_x D_y) = (1/2d)√((1 ± 10ε)(1 ± 10ε))`); the
text's "α = 20ε" on p.178 contradicts that computation (recorded correction). The sign is `+`
exactly when `b = (Mx)_i`. `|ψ_x⟩` of Lemma 7.5.9 is `agnosticExampleState (agnHardDist M ε x)`. -/
noncomputable def agnHardDist {d k : ℕ} (M : Matrix (Fin d) (Fin k) (ZMod 2)) (ε : ℝ)
    (x : Fin k → ZMod 2) : Fin d × Bool → ℝ :=
  fun p => (1 + 10 * ε * (if p.2 = codeConcept M x p.1 then 1 else -1)) / (2 * (d : ℝ))

/-! ### Sanity tests -/

example {d k : ℕ} (M : Matrix (Fin d) (Fin k) (ZMod 2)) : codeConcept M 0 = fun _ => false := by
  funext i
  simp [codeConcept]

example {d k : ℕ} (M : Matrix (Fin d) (Fin k) (ZMod 2)) (x : Fin k → ZMod 2) :
    pacHardConcept M x 0 = false := rfl

example {d k : ℕ} (M : Matrix (Fin d) (Fin k) (ZMod 2)) (x : Fin k → ZMod 2) (i : Fin d) :
    pacHardConcept M x i.succ = codeConcept M x i := rfl

theorem pacHardDist_sum {d : ℕ} (hd : 1 ≤ d) (ε : ℝ) : ∑ i, pacHardDist d ε i = 1 := by
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  rw [Fin.sum_univ_succ]
  simp only [pacHardDist, Fin.cons_zero, Fin.cons_succ, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

theorem agnHardDist_sum {d k : ℕ} (hd : 1 ≤ d) (M : Matrix (Fin d) (Fin k) (ZMod 2)) (ε : ℝ)
    (x : Fin k → ZMod 2) : ∑ p, agnHardDist M ε x p = 1 := by
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have h : ∀ i : Fin d, ∑ b : Bool, agnHardDist M ε x (i, b) = 1 / (d : ℝ) := by
    intro i
    rw [Fintype.sum_bool]
    cases h : codeConcept M x i <;> simp [agnHardDist, h] <;> field_simp <;> ring
  rw [Fintype.sum_prod_type]
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

end QAlgorithms.Learning


