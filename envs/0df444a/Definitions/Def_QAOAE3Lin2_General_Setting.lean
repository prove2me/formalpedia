-- Prove2me | Definitions.Def_QAOAE3Lin2_General_Setting
-- name    : QAOAE3Lin2_General_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T09:01:37.59203+00:00
-- url     : https://prove2.me/theorems/c94c3405-c3a9-42ce-a034-f48267ab1845
-- title:
--   §I–II, (1)–(6), (15)–(21), (25)–(27), (40), pp. 2–8 — Max E3LIN2 instances, the p = 1 QAOA state, expected satisfied count, c-polynomials, P^k, R^k and the angle grid
-- statement:
--   **Instances.** An instance of Max E3LIN2 on $n$ bits has $m$ equations. Equation $i$ is
--   $$x_a + x_b + x_c \equiv r_i \pmod 2$$
--   on a triple $a<b<c$ of distinct bits, with right-hand side $r_i\in\{0,1\}$. No triple carries two equations. The instance has **bounded occurrence $D$** if every bit lies in at most $D+1$ equations.
--
--   **Spins and signs.** For a string $x\in\{0,1\}^n$ write $z_v=(-1)^{x_v}$, the eigenvalue of $Z_v$ on $|x\rangle$. Write $d_i=(-1)^{r_i}$, the paper's $d_{abc}$. Equation $i$ is satisfied by $x$ exactly when $z_az_bz_c=d_i$, so its clause operator is $\tfrac12(1+d_iZ_aZ_bZ_c)$, and the number of satisfied equations is the diagonal operator $C(z)$.
--
--   **The QAOA state.** With $B=\sum_v X_v$ and $|s\rangle$ the uniform superposition,
--   $$|\gamma,\beta\rangle=e^{-i\beta B}e^{-i\gamma C}|s\rangle .$$
--   The **expected satisfied count** is $\sum_x|\langle x|\gamma,\beta\rangle|^2C(x)$. The **clause correlation** of equation $i$ is $\langle\gamma,\beta|Z_aZ_bZ_c|\gamma,\beta\rangle$. The paper's quantity (7), $\langle-\gamma,\beta|C|-\gamma,\beta\rangle$ with $C=\tfrac12\sum d_{abc}Z_aZ_bZ_c$, equals the expected satisfied count at $-\gamma$ minus $m/2$.
--
--   **The c-polynomials.** Write $E_z$ for the average over uniform strings. For equation $i$ and each of its three bits $v$ (roles $1,2,3$), let $c_v(z)=\sum d_j z_az_b$ be the sum over the other equations $j$ that share **exactly** the bit $v$ with equation $i$, where $a,b$ are the two other bits of $j$ (the paper's (21)). The number of terms is $D_v$.
--
--   **The expansion.** For equation $i$ with sign $d$ and polynomials $c_1,c_2,c_3$, the right-hand side of (25) is
--   $$S_i(\gamma)=\tfrac18 d\,E_z\big[\sin(\gamma(d+c_1+c_2+c_3))+\sin(\gamma(d+c_1-c_2-c_3))+\sin(\gamma(d-c_1+c_2-c_3))+\sin(\gamma(d-c_1-c_2+c_3))\big].$$
--   The polynomial (27) is
--   $$P^k_i(\gamma)=\tfrac18 d\sum_{j=3,5,\dots}^{k}\frac{\gamma^j(-1)^{(j-1)/2}}{j!}E_z\big[(d+c_1+c_2+c_3)^j+\dots\big],$$
--   with the same four sign patterns. The remainder $R^k_i(\gamma)=S_i(\gamma)-\tfrac12d^2\gamma-P^k_i(\gamma)$ is defined by (26), and $P^k(\gamma)=\sum_iP^k_i(\gamma)$. The angle grid (40) is $\gamma_r=\cos(\pi r/k)/(10D^{1/2})$ for $r=0,\dots,k$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note.** Strings are `Qubits n = Fin n → Bool`, with `true` the bit $1$. The state's phase operator is the full count $C(z)=m/2+\tfrac12\sum d_{abc}z_az_bz_c$, not the paper's (6). The two differ by the constant $m/2$, so the states differ by the global phase $e^{-i\gamma m/2}$ and every probability is unchanged. $E_z$ is the average over all $2^n$ strings; the paper averages over the bits occurring in $c_1,c_2,c_3$ only, which gives the same number because the integrands depend on those bits only. The triple condition (strictly increasing, injective family) encodes (6)'s $a<b<c$ and $d_{abc}\in\{0,\pm1\}$. Roles $0,1,2$ in Lean are the paper's bits $1,2,3$. The term $z_az_b$ of $c_v$ is computed as $z_az_bz_v\cdot z_v$, using $z_v^2=1$. The quantum layer (`act`, `prob`, `uniformState`, `problemHamiltonian`, `qaoaMixer`, `qaoaUnitary`) is reused from the published `QAlgorithms` definitions.
-- source:
--   Farhi, Goldstone, Gutmann, A Quantum Approximate Optimization Algorithm Applied to a Bounded Occurrence Constraint Problem, arXiv:1412.6062v2, pp. 2–8, Sections I–II, (1)–(6), (15), (19)–(21), (25)–(27), (40)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Adiabatic

namespace QAOAE3Lin2.General

open QAlgorithms

/-! # Max E3LIN2 with bounded occurrence and the level-one QAOA

Farhi, Goldstone, Gutmann, arXiv:1412.6062v2, §I–II, pp. 2–8.

An instance has `n` bits and `m` equations. Equation `i : Fin m` is
`x_a + x_b + x_c ≡ rhs i (mod 2)` on the triple `tri i = (a, b, c)`. A basis string is
`x : Qubits n = Fin n → Bool`, and `x v = true` is the bit `x_v = 1`.

Conventions:
* `spin x v = (-1)^{x_v}` is the eigenvalue `z_v` of `Z_v` on `|x⟩`, and `sgn rhs i = (-1)^{rhs i}`
  is the paper's `d_abc` (`+1` for the equation `= 0`). Equation `i` is satisfied by `x` iff the
  product of its three spins equals `sgn rhs i`, so its clause operator (5) is `½(1 + d Z_a Z_b Z_c)`.
* The phase operator of the state is the full count `satCount = m/2 + C`, with `C` the paper's (6).
  The two differ by the constant `m/2`, so `e^{-iγ·satCount}` and `e^{-iγC}` differ by the global
  phase `e^{-iγm/2}`, and every measurement probability is the same.
* `avgZ` averages over all `2ⁿ` strings. The paper's `E_z` averages over the bits `Q` occurring in
  `c₁, c₂, c₃` (p. 5); every integrand used here depends on those bits only, so both averages agree.
-/

/-- Bit `v` occurs in the triple `t = (a, b, c)`. -/
def onTriple {n : ℕ} (t : Fin n × Fin n × Fin n) (v : Fin n) : Prop :=
  v = t.1 ∨ v = t.2.1 ∨ v = t.2.2

instance {n : ℕ} (t : Fin n × Fin n × Fin n) (v : Fin n) : Decidable (onTriple t v) := by
  unfold onTriple; infer_instance

/-- §II, p. 3–4, (6): every equation is on three bits `a < b < c` (strictly increasing, so three
distinct bits: "each clause contains exactly 3 variables"), and no triple carries two equations
(injectivity: `d_abc ∈ {0, ±1}` in (6)). -/
def IsTripleFamily {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n) : Prop :=
  (∀ i, (tri i).1 < (tri i).2.1 ∧ (tri i).2.1 < (tri i).2.2) ∧ Function.Injective tri

/-- §I, p. 3: "every bit is in no more than `D + 1` equations". -/
def BoundedOccurrence {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n) (D : ℕ) : Prop :=
  ∀ v : Fin n, (Finset.univ.filter fun i => onTriple (tri i) v).card ≤ D + 1

/-- The eigenvalue `z_v = (-1)^{x_v}` of `Z_v` on the basis state `|x⟩` (`Z|0⟩ = |0⟩`). -/
def spin {n : ℕ} (x : Qubits n) (v : Fin n) : ℝ :=
  if x v then -1 else 1

/-- (6): the sign `d_abc` of equation `i`: `+1` for the equation `x_a + x_b + x_c = 0`, `-1` for
`= 1`. -/
def sgn {m : ℕ} (rhs : Fin m → Bool) (i : Fin m) : ℝ :=
  if rhs i then -1 else 1

/-- (1): `C(z)`, the number of equations satisfied by the string `x`. -/
def satCount {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n) (rhs : Fin m → Bool)
    (x : Qubits n) : ℝ :=
  ((Finset.univ.filter fun i =>
    (xor (xor (x (tri i).1) (x (tri i).2.1)) (x (tri i).2.2)) = rhs i).card : ℝ)

/-- (4): the level-one QAOA state `|γ, β⟩ = e^{-iβB} e^{-iγC} |s⟩`, with `γ` the phase angle and
`β` the mixer angle (the published `qaoaUnitary f p β θ` takes the mixer angles first). The phase
operator is `satCount`, which differs from (6)'s `C` by the constant `m/2` (a global phase). -/
noncomputable def qaoaState1 {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n)
    (rhs : Fin m → Bool) (γ β : ℝ) : EuclideanSpace ℂ (Qubits n) :=
  act (qaoaUnitary (satCount tri rhs) 1 (fun _ => β) (fun _ => γ)) (uniformState (Qubits n))

/-- The expected number of satisfied equations when `|γ, β⟩` is measured in the computational
basis: `Σ_x |⟨x|γ, β⟩|² C(x)`. The paper's (7) at `γ` is `expSat tri rhs (-γ) β - m/2`. -/
noncomputable def expSat {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n) (rhs : Fin m → Bool)
    (γ β : ℝ) : ℝ :=
  ∑ x, prob (qaoaState1 tri rhs γ β) x * satCount tri rhs x

/-- `⟨γ, β| Z_a Z_b Z_c |γ, β⟩` for the triple `(a, b, c)` of equation `i` (the `Z`'s are diagonal,
so this is exact). -/
noncomputable def corr {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n) (rhs : Fin m → Bool)
    (i : Fin m) (γ β : ℝ) : ℝ :=
  ∑ x, prob (qaoaState1 tri rhs γ β) x *
    (spin x (tri i).1 * spin x (tri i).2.1 * spin x (tri i).2.2)

/-- `E_z f`: the classical average of `f` over the `2ⁿ` strings, uniformly weighted. -/
noncomputable def avgZ {n : ℕ} (f : Qubits n → ℝ) : ℝ :=
  (Fintype.card (Qubits n) : ℝ)⁻¹ * ∑ x, f x

/-- The bit playing role `r` in the triple `t = (a, b, c)`: role `0 ↦ a`, `1 ↦ b`, `2 ↦ c`. Roles
`0, 1, 2` are the paper's bits `1, 2, 3` of the central clause. -/
def roleBit {n : ℕ} (t : Fin n × Fin n × Fin n) (r : Fin 3) : Fin n :=
  match r with
  | 0 => t.1
  | 1 => t.2.1
  | 2 => t.2.2

/-- (15): equation `j` shares exactly the bit in role `r` with equation `i` (and no other bit of
`i`). These are the clauses of `C_r` in (15); clauses sharing two bits with `i` (`C₁₂` etc.) do
not enter (16). -/
def sharesOnly {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n) (i j : Fin m) (r : Fin 3) : Prop :=
  j ≠ i ∧ onTriple (tri j) (roleBit (tri i) r) ∧ ∀ r' ≠ r, ¬ onTriple (tri j) (roleBit (tri i) r')

instance {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n) (i j : Fin m) (r : Fin 3) :
    Decidable (sharesOnly tri i j r) := by
  unfold sharesOnly; infer_instance

/-- (21): `c_r(z) = Σ_{a<b} d_{rab} z_a z_b`, the sum over the equations `j` that share exactly the
role-`r` bit `v` of equation `i`, each contributing its sign times the product of its two other
spins. That product is written as (product of the three spins of `j`) × `spin x v`, which equals
`z_a z_b` because `spin x v ^ 2 = 1`. -/
noncomputable def cPoly {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n) (rhs : Fin m → Bool)
    (i : Fin m) (r : Fin 3) (x : Qubits n) : ℝ :=
  ∑ j, if sharesOnly tri i j r then
    sgn rhs j * (spin x (tri j).1 * spin x (tri j).2.1 * spin x (tri j).2.2 *
      spin x (roleBit (tri i) r))
  else 0

/-- (49): `D_r`, the number of terms of `c_r`. -/
def termCount {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n) (i : Fin m) (r : Fin 3) : ℕ :=
  (Finset.univ.filter fun j => sharesOnly tri i j r).card

/-- (25): the right-hand side
`⅛ d E_z[sin(γ(d + c₁ + c₂ + c₃)) + sin(γ(d + c₁ − c₂ − c₃)) + sin(γ(d − c₁ + c₂ − c₃))
+ sin(γ(d − c₁ − c₂ + c₃))]` for equation `i`, with `d = sgn rhs i` and `c₁, c₂, c₃` the
polynomials `cPoly tri rhs i 0`, `… 1`, `… 2`. -/
noncomputable def clauseSin {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n)
    (rhs : Fin m → Bool) (i : Fin m) (γ : ℝ) : ℝ :=
  (1 / 8) * sgn rhs i * avgZ (fun x =>
    let d := sgn rhs i
    let c₁ := cPoly tri rhs i 0 x
    let c₂ := cPoly tri rhs i 1 x
    let c₃ := cPoly tri rhs i 2 x
    Real.sin (γ * (d + c₁ + c₂ + c₃)) + Real.sin (γ * (d + c₁ - c₂ - c₃)) +
      Real.sin (γ * (d - c₁ + c₂ - c₃)) + Real.sin (γ * (d - c₁ - c₂ + c₃)))

/-- (27): `P^k(γ) = ⅛ d Σ_{j = 3, 5, …, k} (γ^j (−1)^{(j−1)/2} / j!) E_z[(d + c₁ + c₂ + c₃)^j + …]`,
the four sign patterns of (25). The index runs over the odd `j` with `3 ≤ j ≤ k`; for odd `j`
the natural-number quotient `(j − 1)/2` is exact. -/
noncomputable def Pk {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n) (rhs : Fin m → Bool)
    (i : Fin m) (k : ℕ) (γ : ℝ) : ℝ :=
  (1 / 8) * sgn rhs i *
    ∑ j ∈ (Finset.range (k + 1)).filter (fun j => 3 ≤ j ∧ Odd j),
      γ ^ j * (-1 : ℝ) ^ ((j - 1) / 2) / (j.factorial : ℝ) *
        avgZ (fun x =>
          let d := sgn rhs i
          let c₁ := cPoly tri rhs i 0 x
          let c₂ := cPoly tri rhs i 1 x
          let c₃ := cPoly tri rhs i 2 x
          (d + c₁ + c₂ + c₃) ^ j + (d + c₁ - c₂ - c₃) ^ j + (d - c₁ + c₂ - c₃) ^ j +
            (d - c₁ - c₂ + c₃) ^ j)

/-- (26), read as the definition of the remainder: (25) `= ½ d² γ + P^k(γ) + R^k(γ)`. (`d² = 1`,
p. 7; the factor is kept as printed.) -/
noncomputable def Rk {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n) (rhs : Fin m → Bool)
    (i : Fin m) (k : ℕ) (γ : ℝ) : ℝ :=
  clauseSin tri rhs i γ - (1 / 2) * sgn rhs i ^ 2 * γ - Pk tri rhs i k γ

/-- p. 8, after (35): `P^k(γ)`, "the sum of the `m` polynomials `P^k_abc(γ)`". -/
noncomputable def PkSum {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n) (rhs : Fin m → Bool)
    (k : ℕ) (γ : ℝ) : ℝ :=
  ∑ i, Pk tri rhs i k γ

/-- (40): the grid angle `γ_r = (1/(10 D^{1/2})) cos(πr/k)`, for `r = 0, …, k`. -/
noncomputable def gammaGrid (D k r : ℕ) : ℝ :=
  Real.cos (Real.pi * r / k) / (10 * Real.sqrt D)

end QAOAE3Lin2.General


