-- Prove2me | Definitions.Def_SDPT3_ScaleInv_Setting
-- name    : SDPT3_ScaleInv_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T03:12:31.336619+00:00
-- url     : https://prove2.me/theorems/ecd5510f-9df9-4b79-8fa2-3b4392a78523
-- title:
--   (17)–(21), (4), (7)–(8), (11)–(12), (22) — second-order-cone blocks, Arw, γ, the HKM and NT scalings G, and the Newton system (4) of a pure SOCP
-- statement:
--   This file sets up the objects of §2 of Tütüncü, Toh and Todd (2003) for a **pure second-order cone program** (no semidefinite and no linear blocks, $n_s = n_l = 0$).
--
--   **Blocks and the cone.** There are $n_q$ blocks; block $i$ has dimension $q_i = d_i + 1 \ge 1$. A block vector $x_i \in \mathbb R^{q_i}$ is split as in (17) into its first coordinate $x_i^0$ and the remaining subvector $x_i^1 \in \mathbb R^{q_i - 1}$. With $\bar J = \operatorname{diag}(1, -I)$ and $J = -\bar J = \operatorname{diag}(-1, I)$ (the $J_i$ of (25)), set
--   $$\gamma^2(x) = x^\top \bar J x = (x^0)^2 - \langle x^1, x^1\rangle, \qquad \gamma(x) = \sqrt{\gamma^2(x)} \quad (18).$$
--   The second-order cone is $K_q = \{x : x^0 \ge \|x^1\|_2\}$; its interior is $\{x : x^0 > 0,\ \gamma^2(x) > 0\}$.
--
--   **Arrow matrix and the two scalings.** $\operatorname{Arw}(v) = \begin{pmatrix} v^0 & (v^1)^\top \\ v^1 & v^0 I \end{pmatrix}$ and $e_1$ is the first unit vector (p. 6). The HKM scaling (19) is
--   $$G^{\mathrm{HKM}}(z) = \begin{pmatrix} z^0 & (z^1)^\top \\ z^1 & \gamma(z) I + \dfrac{z^1 (z^1)^\top}{\gamma(z) + z^0} \end{pmatrix}.$$
--   The NT scaling (20)–(21) uses $\omega = \sqrt{\gamma(z)/\gamma(x)}$, $\xi = (z^0/\omega + \omega x^0;\ z^1/\omega - \omega x^1)$, $t = \xi/\gamma(\xi)$ and
--   $$G^{\mathrm{NT}}(x,z) = \omega \begin{pmatrix} t^0 & (t^1)^\top \\ t^1 & I + \dfrac{t^1 (t^1)^\top}{1 + t^0} \end{pmatrix}.$$
--
--   **Newton blocks (7)–(8).** For a block scaling $G$: $\mathcal E = \operatorname{Arw}(G^{-1} z)\, G$, $\mathcal F = \operatorname{Arw}(G x)\, G^{-1}$ and $T_G(x,z) = \operatorname{Arw}(Gx)(G^{-1} z)$.
--
--   **The Newton system (4).** The data are matrices $A_i \in \mathbb R^{q_i \times m}$ (the blocks of $A^\top$), $b \in \mathbb R^m$ and $c_i \in \mathbb R^{q_i}$; the primal constraint is $\sum_i A_i^\top x_i = b$ and the dual constraint is $A_i y + z_i = c_i$. Given an iterate $(x, y, z)$, a centering parameter $\sigma$ and $\mu = \langle x, z\rangle / n_q$, a triple $(\Delta x, \Delta y, \Delta z)$ is a **search direction** of the chosen kind (HKM or NT, with $G_i$ from (19) or (21)) if
--   $$A_i \Delta y + \Delta z_i = (R_d)_i := c_i - z_i - A_i y,\qquad \sum_i A_i^\top \Delta x_i = r_p := b - \sum_i A_i^\top x_i,\qquad \mathcal E_i \Delta x_i + \mathcal F_i \Delta z_i = (R_c)_i := \sigma\mu\, e_1 - T_{G_i}(x_i, z_i)$$
--   for every block $i$.
--
--   **Schur complement quantities (11), (12), (22).** $M_i = A_i^\top \mathcal E_i^{-1} \mathcal F_i A_i$, $M = \sum_i M_i$ and $h = r_p - \sum_i A_i^\top \mathcal E_i^{-1}\big((R_c)_i - \mathcal F_i (R_d)_i\big)$.
--
--   **Automorphisms.** A matrix $F$ belongs to the automorphism group $\mathcal G$ of $K_q$ when $F^\top \bar J F = \lambda^2 \bar J$ for some $\lambda > 0$ and $F_{00} > 0$.
--
--   These are the objects Proposition 1 speaks about: the search directions are defined through the raw system (4), and every closed-form identity of §2.3.2 is a separate theorem.
--
--   **Formalization Note** A block vector is `Fin (d i + 1) → ℝ`; $x^0$ is index `0` and $x^1$ the indices `Fin.succ j`. Mathlib's norm on `Fin k → ℝ` is the sup norm, so every Euclidean quantity is written through $\bar J$. The interior is encoded by the strict inequalities $x^0 > 0$, $\gamma^2(x) > 0$ (the algorithm keeps its iterates there, p. 3). $\mu$ uses $n = n_q$, the number of blocks (p. 5, $n = \sum_j s_j + n_q + n_l$). The automorphism group is given by its standard algebraic description (positive multiples of orthochronous Lorentz transformations), not by the set-theoretic condition $F K = K$; for every $q \ge 1$ the two agree. Matrix inverses are Mathlib's `Matrix.inv`, which is $0$ on singular input; for interior iterates all inverted matrices are invertible, which the theorems of the mission state or use. The names `calE`, `calF` stand for $\mathcal E$, $\mathcal F$; `Fsc` in the theorems is the scaling $F$ of the proof.
-- source:
--   Tütüncü, Toh & Todd, Solving semidefinite-quadratic-linear programs using SDPT3, Math. Program. 95 (2003) 189–217; authors' copy, pp. 2–8, (P), (D), (4), (7), (8), (11), (12), (17)–(22); p. 12 (automorphism group 𝒢ᵢ)

import Mathlib

namespace SDPT3.ScaleInv

open Matrix

/-! Tütüncü, Toh & Todd (2003), authors' copy, pp. 2–8: second-order-cone blocks, the arrow
operator, γ, the HKM and NT scaling matrices (19)–(21), the blocks ℰ, ℱ and T_G of (7)–(8), and the
Newton system (4) of a pure second-order cone program (n_s = n_l = 0).

Convention: a block of dimension q = k + 1 is `Fin (k + 1) → ℝ`; the coordinate x⁰ of (17) sits at
index `0` and the subvector x¹ at the indices `Fin.succ j`. All norms are Euclidean and are written
out through `Jbar`. -/

/-- `J̄ = diag(1, −I)` on `ℝ^{k+1}` (proof of Proposition 1, p. 12: `J̄ = −J`). -/
def Jbar (k : ℕ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
  Matrix.diagonal (fun a => if a = 0 then 1 else -1)

/-- `J = diag(−1, I)` of (25), p. 9. -/
def J (k : ℕ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ := -Jbar k

/-- `γ²(v) = (v⁰)² − ⟨v¹, v¹⟩`, the radicand of (18). -/
def gammaSq {k : ℕ} (v : Fin (k + 1) → ℝ) : ℝ := v ⬝ᵥ (Jbar k *ᵥ v)

/-- `γ(v) = √((v⁰)² − ⟨v¹, v¹⟩)`, (18), p. 7. -/
noncomputable def gam {k : ℕ} (v : Fin (k + 1) → ℝ) : ℝ := Real.sqrt (gammaSq v)

/-- Strict interior of the second-order cone `K_q^{k+1} = {x : x⁰ ≥ ‖x¹‖}`:
`x⁰ > 0` and `(x⁰)² − ⟨x¹, x¹⟩ > 0`, i.e. `x⁰ > ‖x¹‖`. -/
def socInt {k : ℕ} (v : Fin (k + 1) → ℝ) : Prop := 0 < v 0 ∧ 0 < gammaSq v

/-- The arrow matrix `Arw(v) = [v⁰ (v¹)ᵀ; v¹ v⁰ I]`, p. 6. -/
def arw {k : ℕ} (v : Fin (k + 1) → ℝ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
  Matrix.of fun a b =>
    if a = 0 then v b else if b = 0 then v a else if a = b then v 0 else 0

/-- The first unit vector `e₁ ∈ ℝ^{k+1}`, p. 6. -/
def e1 (k : ℕ) : Fin (k + 1) → ℝ := Pi.single 0 1

/-- The HKM scaling block (19), p. 7:
`G = [z⁰ (z¹)ᵀ; z¹ γ(z)I + z¹(z¹)ᵀ/(γ(z) + z⁰)]`. -/
noncomputable def GHKM {k : ℕ} (z : Fin (k + 1) → ℝ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
  Matrix.of fun a b =>
    if a = 0 then z b
    else if b = 0 then z a
    else (if a = b then gam z else 0) + z a * z b / (gam z + z 0)

/-- `ω = √(γ(z)/γ(x))`, (20), p. 7. -/
noncomputable def omegaNT {k : ℕ} (x z : Fin (k + 1) → ℝ) : ℝ := Real.sqrt (gam z / gam x)

/-- `ξ = [z⁰/ω + ω x⁰; z¹/ω − ω x¹]`, (20), p. 7. -/
noncomputable def xiNT {k : ℕ} (x z : Fin (k + 1) → ℝ) : Fin (k + 1) → ℝ :=
  fun a => if a = 0 then z a / omegaNT x z + omegaNT x z * x a
    else z a / omegaNT x z - omegaNT x z * x a

/-- `t = ξ / γ(ξ)`, (21), p. 8. -/
noncomputable def tNT {k : ℕ} (x z : Fin (k + 1) → ℝ) : Fin (k + 1) → ℝ :=
  (gam (xiNT x z))⁻¹ • xiNT x z

/-- The NT scaling block (21), p. 8: `G = ω [t⁰ (t¹)ᵀ; t¹ I + t¹(t¹)ᵀ/(1 + t⁰)]`. -/
noncomputable def GNT {k : ℕ} (x z : Fin (k + 1) → ℝ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
  omegaNT x z • Matrix.of fun a b =>
    if a = 0 then tNT x z b
    else if b = 0 then tNT x z a
    else (if a = b then 1 else 0) + tNT x z a * tNT x z b / (1 + tNT x z 0)

/-- The two search directions of §2.2: HKM and NT. -/
inductive Dir
  | hkm
  | nt

/-- The scaling block `G` of the chosen direction: (19) for HKM (depends on `z` only), (21) for NT. -/
noncomputable def Gdir {k : ℕ} : Dir → (Fin (k + 1) → ℝ) → (Fin (k + 1) → ℝ) →
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ
  | .hkm, _, z => GHKM z
  | .nt, x, z => GNT x z

/-- `ℰ = Arw(G⁻¹z) G`, (8), p. 6. -/
noncomputable def calE {k : ℕ} (G : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) (z : Fin (k + 1) → ℝ) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
  arw (G⁻¹ *ᵥ z) * G

/-- `ℱ = Arw(Gx) G⁻¹`, (8), p. 6. -/
noncomputable def calF {k : ℕ} (G : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) (x : Fin (k + 1) → ℝ) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
  arw (G *ᵥ x) * G⁻¹

/-- One block of `T_G(x, z)`: `Arw(Gx)(G⁻¹z)`, (7), p. 6. -/
noncomputable def TG {k : ℕ} (G : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) (x z : Fin (k + 1) → ℝ) :
    Fin (k + 1) → ℝ :=
  arw (G *ᵥ x) *ᵥ (G⁻¹ *ᵥ z)

section Blocks

variable {nq m : ℕ} {d : Fin nq → ℕ}

/-- `µ = ⟨x, z⟩ / n` with `n = n_q` for a pure SOCP, p. 5. -/
noncomputable def muSOC (x z : (i : Fin nq) → Fin (d i + 1) → ℝ) : ℝ :=
  (∑ i, x i ⬝ᵥ z i) / nq

/-- Block `i` of the dual residual `R_d = c − z − Aᵀy`, (4); `(Aᵀy)ᵢ = A_i^q y`. -/
def Rd (A : (i : Fin nq) → Matrix (Fin (d i + 1)) (Fin m) ℝ) (c z : (i : Fin nq) → Fin (d i + 1) → ℝ)
    (y : Fin m → ℝ) (i : Fin nq) : Fin (d i + 1) → ℝ :=
  c i - z i - A i *ᵥ y

/-- The primal residual `r_p = b − Ax`, (4), with `Ax = Σᵢ (A_i^q)ᵀ xᵢ`. -/
def rp (A : (i : Fin nq) → Matrix (Fin (d i + 1)) (Fin m) ℝ) (b : Fin m → ℝ)
    (x : (i : Fin nq) → Fin (d i + 1) → ℝ) : Fin m → ℝ :=
  b - ∑ i, (A i)ᵀ *ᵥ x i

/-- Block `i` of `R_c^q = σµe^q − T_G(x^q, z^q)`, (4), with `G` the scaling of `dir`. -/
noncomputable def Rc (dir : Dir) (σ : ℝ) (x z : (i : Fin nq) → Fin (d i + 1) → ℝ) (i : Fin nq) :
    Fin (d i + 1) → ℝ :=
  (σ * muSOC x z) • e1 (d i) - TG (Gdir dir (x i) (z i)) (x i) (z i)

/-- The Newton system (4), p. 5, of a pure SOCP (`n_s = n_l = 0`), with `ℰ`, `ℱ`, `T_G` from (7)–(8)
and `G` from (19) (HKM) or (21) (NT):
`Aᵀ∆y + ∆z = R_d`, `A∆x = r_p`, `ℰᵢ∆xᵢ + ℱᵢ∆zᵢ = (R_c)ᵢ` for every block `i`. -/
def IsNewtonDir (dir : Dir) (A : (i : Fin nq) → Matrix (Fin (d i + 1)) (Fin m) ℝ) (b : Fin m → ℝ)
    (c x : (i : Fin nq) → Fin (d i + 1) → ℝ) (y : Fin m → ℝ) (z : (i : Fin nq) → Fin (d i + 1) → ℝ)
    (σ : ℝ) (Δx : (i : Fin nq) → Fin (d i + 1) → ℝ) (Δy : Fin m → ℝ)
    (Δz : (i : Fin nq) → Fin (d i + 1) → ℝ) : Prop :=
  (∀ i, A i *ᵥ Δy + Δz i = Rd A c z y i) ∧
  (∑ i, (A i)ᵀ *ᵥ Δx i = rp A b x) ∧
  (∀ i, calE (Gdir dir (x i) (z i)) (z i) *ᵥ Δx i + calF (Gdir dir (x i) (z i)) (x i) *ᵥ Δz i
      = Rc dir σ x z i)

/-- The summand `M_i^q = (A_i^q)ᵀ (ℰᵢ)⁻¹ ℱᵢ A_i^q` of (22), p. 8, for a block with data `Ai`. -/
noncomputable def Mblock {k : ℕ} (G : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)
    (Ai : Matrix (Fin (k + 1)) (Fin m) ℝ) (x z : Fin (k + 1) → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  Aiᵀ * ((calE G z)⁻¹ * calF G x) * Ai

/-- The Schur complement matrix `M = Σᵢ M_i^q`, (11) and (22). -/
noncomputable def schurM (dir : Dir) (A : (i : Fin nq) → Matrix (Fin (d i + 1)) (Fin m) ℝ)
    (x z : (i : Fin nq) → Fin (d i + 1) → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  ∑ i, Mblock (Gdir dir (x i) (z i)) (A i) (x i) (z i)

/-- The right-hand side `h = r_p − Σᵢ (A_i^q)ᵀ (ℰᵢ)⁻¹ ((R_c)ᵢ − ℱᵢ (R_d)ᵢ)`, (12). -/
noncomputable def schurH (dir : Dir) (A : (i : Fin nq) → Matrix (Fin (d i + 1)) (Fin m) ℝ)
    (b : Fin m → ℝ) (c x : (i : Fin nq) → Fin (d i + 1) → ℝ) (y : Fin m → ℝ)
    (z : (i : Fin nq) → Fin (d i + 1) → ℝ) (σ : ℝ) : Fin m → ℝ :=
  rp A b x - ∑ i, (A i)ᵀ *ᵥ ((calE (Gdir dir (x i) (z i)) (z i))⁻¹ *ᵥ
      (Rc dir σ x z i - calF (Gdir dir (x i) (z i)) (x i) *ᵥ Rd A c z y i))

end Blocks

/-- The automorphism group `𝒢` of `K_q^{k+1}` (proof of Proposition 1, p. 12), in its standard
algebraic description: `F` is a positive multiple of an orthochronous Lorentz transformation,
`FᵀJ̄F = λ²J̄` for some `λ > 0`, and `F₀₀ > 0`. -/
def IsSOCAut {k : ℕ} (F : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) : Prop :=
  ∃ l : ℝ, 0 < l ∧ Fᵀ * Jbar k * F = l ^ 2 • Jbar k ∧ 0 < F 0 0

end SDPT3.ScaleInv


