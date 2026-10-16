-- Prove2me | Definitions.Def_QAOAE3Lin2_Typical_Setting
-- name    : QAOAE3Lin2_Typical_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T10:58:12.079289+00:00
-- url     : https://prove2.me/theorems/5e99c2e7-6d45-4a1c-9c7d-9e3fce306a69
-- title:
--   §I–III, (1)–(6), (19)–(21), (25), (46), (55), pp. 2–11 — Max E3LIN2 instances, the p = 1 QAOA state, expected satisfied count, c-polynomials and averages over the d's
-- statement:
--   The objects of the level-one QAOA analysis of Max E3LIN2 with bounded occurrence, and of its average over random right-hand sides.
--
--   **Instances.** An instance on $n$ bits with $m$ equations is a list of triples $(a_i,b_i,c_i)$, $i=1,\dots,m$, of bits together with right-hand sides $r_i\in\{0,1\}$; equation $i$ reads
--   $$x_{a_i}+x_{b_i}+x_{c_i}\equiv r_i \pmod 2 .$$
--   The triples form an **E3LIN2 family** when every triple has $a_i<b_i<c_i$ (three distinct bits) and no triple occurs twice (so that each $d_{abc}\in\{0,\pm1\}$ in (6)). The instance has **occurrence at most $D+1$** when every bit lies in at most $D+1$ of the triples.
--
--   **Spins and signs.** For a bit string $x$ write $z_v=(-1)^{x_v}$ for the eigenvalue of $Z_v$ on $|x\rangle$, and $d_i=(-1)^{r_i}$ for the sign of equation $i$ (the paper's $d_{abc}$, equal to $+1$ for the equation "$=0$"). Equation $i$ is satisfied by $x$ exactly when $z_{a_i}z_{b_i}z_{c_i}=d_i$.
--
--   **The QAOA state.** $C(x)$ is the number of equations satisfied by $x$, viewed as the diagonal operator $C|x\rangle=C(x)|x\rangle$; $B=\sum_v X_v$ is the mixer; $|s\rangle$ is the uniform superposition. For angles $\gamma,\beta$,
--   $$|\gamma,\beta\rangle=e^{-i\beta B}e^{-i\gamma C}|s\rangle .$$
--   The **expected number of satisfied equations** is $\sum_x |\langle x|\gamma,\beta\rangle|^2\,C(x)$, and the **correlation** of equation $i$ is $\langle\gamma,\beta|Z_{a_i}Z_{b_i}Z_{c_i}|\gamma,\beta\rangle=\sum_x|\langle x|\gamma,\beta\rangle|^2 z_{a_i}z_{b_i}z_{c_i}$.
--
--   **Averages.** $\mathbb E_z$ is the uniform average over all $2^n$ bit strings; $\mathbb E_d$ is the uniform average over the $2^m$ right-hand-side vectors $r\in\{0,1\}^m$ on the fixed triples, i.e. over the instances of (46); $\mathrm{Var}_d\,g=\mathbb E_d[(g-\mathbb E_d g)^2]$.
--
--   **The $c$-polynomials (19)–(21).** Label the bits of equation $i$ by roles $1,2,3$. Equation $j$ *shares exactly role $\rho$* with $i$ when $j\ne i$ and $j$ contains the role-$\rho$ bit of $i$ and none of its other two bits. Then
--   $$c_\rho(z)=\sum_{j\ \text{shares exactly role }\rho} d_j\, z_{a}z_{b},$$
--   where $a,b$ are the two other bits of equation $j$, and $D_\rho$ is the number of terms of $c_\rho$.
--
--   **The single-clause expressions.** The right-hand side of (25) is
--   $$\tfrac18 d_i\,\mathbb E_z\big[\sin(\gamma(d_i+c_1+c_2+c_3))+\sin(\gamma(d_i+c_1-c_2-c_3))+\sin(\gamma(d_i-c_1+c_2-c_3))+\sin(\gamma(d_i-c_1-c_2+c_3))\big],$$
--   and the summand of (55) is $\tfrac12 d_i\langle-\gamma,\pi/4|Z_{a_i}Z_{b_i}Z_{c_i}|-\gamma,\pi/4\rangle$. The **dependency set** of equation $i$ is $\{i\}$ together with all equations sharing exactly one role with $i$: the $d$'s appearing in (25) for equation $i$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Bit strings are `Fin n → Bool` (`QAlgorithms.Qubits n`), with `true` the bit $1$. The phase operator used in the state is the full count $C(x)$, which equals $m/2$ plus the operator (6) of the paper; the two exponentials differ by the global phase $e^{-i\gamma m/2}$, so every measurement probability is the same. The QAOA unitary is the published `QAlgorithms.qaoaUnitary` at one layer, which takes the mixer angle first. $\mathbb E_z$ averages over all $n$ bits, not only the bits occurring in $c_1,c_2,c_3$; the integrands depend only on those bits, so the value is the same. The product $z_{a}z_{b}$ in $c_\rho$ is computed as the product of the three spins of equation $j$ times the spin of the shared bit, using $z^2=1$.
-- source:
--   Farhi, Goldstone, Gutmann, A Quantum Approximate Optimization Algorithm Applied to a Bounded Occurrence Constraint Problem, arXiv:1412.6062v2, pp. 2–6, Sections I–II, (1)–(6), (19)–(21), (25); pp. 9–11, Section III, (46), (55) and the variance paragraph

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Adiabatic
import Definitions.Def_QAOAE3Lin2_General_Setting

/-!
# Max E3LIN2 with bounded occurrence, the level-one QAOA state, and the instance average

Farhi, Goldstone, Gutmann, *A Quantum Approximate Optimization Algorithm Applied to a Bounded
Occurrence Constraint Problem*, arXiv:1412.6062v2: §I–II (1)–(6), (19)–(21), (25), pp. 2–6;
§III (46), (55), the variance paragraph, pp. 9–11.

Conventions.
* An instance is `tri : Fin m → Fin n × Fin n × Fin n` (the triples) and `rhs : Fin m → Bool`
  (equation `i` is `x_a + x_b + x_c ≡ rhs i (mod 2)` on `tri i = (a, b, c)`).
* The basis index is `QAlgorithms.Qubits n = Fin n → Bool`; `x v = true` is the bit `x_v = 1`, and
  `spin x v = (-1)^{x_v}` is the eigenvalue of `Z_v` on `|x⟩`. `sgn rhs i = (-1)^{rhs i}` is the
  paper's `d_abc` (`+1` for the equation "= 0"). Equation `i` is satisfied by `x` iff the product of
  the three spins equals `sgn rhs i`.
* The phase operator is the full count `satCount = m/2 + C` (C of (6)); `e^{-iγ satCount}` and
  `e^{-iγ C}` differ by the global phase `e^{-iγ m/2}`, so all measurement probabilities agree.
-/

namespace QAOAE3Lin2.Typical

open QAlgorithms

/-- `E_d`: the uniform average over the `2^m` choices of right-hand sides, i.e. over the
instances on the fixed triples (§III, (46), p. 9). -/
noncomputable def avgD {m : ℕ} (g : (Fin m → Bool) → ℝ) : ℝ :=
  (2 ^ m : ℝ)⁻¹ * ∑ rhs, g rhs

/-- The summand of (55) for equation `i`: `½ d_abc ⟨−γ, π/4| Z_a Z_b Z_c |−γ, π/4⟩` (note `−γ`). -/
noncomputable def clauseTerm {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n)
    (rhs : Fin m → Bool) (i : Fin m) (γ : ℝ) : ℝ :=
  (1 / 2) * QAOAE3Lin2.General.sgn rhs i * QAOAE3Lin2.General.corr tri rhs i (-γ) (Real.pi / 4)

/-- p. 11: the equations whose signs `d` appear in (25) for equation `i`: `d_i` itself and the
`d`'s of `c₁, c₂, c₃`. -/
def deps {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n) (i : Fin m) : Finset (Fin m) :=
  insert i (Finset.univ.filter fun j => ∃ r : Fin 3, QAOAE3Lin2.General.sharesOnly tri i j r)

/-- p. 11: the variance over the `2^m` instances (uniform right-hand sides) of a quantity `g`. -/
noncomputable def varD {m : ℕ} (g : (Fin m → Bool) → ℝ) : ℝ :=
  avgD (fun rhs => (g rhs - avgD g) ^ 2)

end QAOAE3Lin2.Typical


