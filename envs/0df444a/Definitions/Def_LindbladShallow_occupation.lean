-- Prove2me | Definitions.Def_LindbladShallow_occupation
-- name    : LindbladShallow_occupation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T04:17:45.363956+00:00
-- url     : https://prove2.me/theorems/2e2d2895-9c09-4abe-af7f-f18e8999ed1a
-- title:
--   Occupation projections, occupation moments and collision gates on system ⊗ baths
-- statement:
--   Consider a system together with baths $b$, each of dimension $d+1$ with vacuum $|0\rangle$. Let $P_b=I-|0\rangle\langle0|_b$ and $P_F=\prod_{b\in F}P_b$. For a counted bath set $\mathcal B_{\mathrm{cat}}$ with occupation operator $N_{\mathrm{cat}}=\sum_{b\in\mathcal B_{\mathrm{cat}}}P_b$, $z^{N_{\mathrm{cat}}}$ and $P_bz^{N_{\mathrm{cat}}-P_b}$ are diagonal in the bath basis. $E_0$ initializes every bath to vacuum. A gate $U$ **touches** $b$ if $[P_b,U]\neq0$, and $a_b=\sum_{j\text{ touches }b}\|[P_b,U_j]\|$.
--
--   The **occupation bounds** of a column $Y$ with nonnegative numbers $a_b$ are
--   1. $\|P_FY\|\le\prod_{b\in F}a_b$ for every $F\subseteq\mathcal B_{\mathrm{cat}}$;
--   2. $Y^\dagger z^{N_{\mathrm{cat}}}Y\preceq\prod_b[1+(z-1)a_b^2]\,I$ for every $z\ge1$;
--   3. $Y^\dagger P_bz^{N_{\mathrm{cat}}-P_b}Y\preceq a_b^2\prod_{c\ne b}[1+(z-1)a_c^2]\,I$ for every $b$ and $z\ge1$.
--
--   A **normalized physical collision gate** is a Hamiltonian gate on the system or a forward/adjoint jump Cayley gate $V_{J,h}^{\pm1}$ on the system and one bath, carrying its duration $h$ and strength $\lambda$.
--
--   These are the objects of Lemma 3.6 and Theorem 3.7.
-- source:
--   Shen, Wu, Yuan, Zhang, Shallow Quantum Circuits for Geometrically Local Lindblad Dynamics, arXiv:2610.05362 (held version, sha256 8f4637ef…), §2.3, p.12; §3.3 and Lemma 3.6, p.19

import Mathlib
import Definitions.Def_LindbladShallow_gksl

open scoped Matrix ComplexOrder

namespace LindbladShallow

/-- The computational basis of a system (basis `σ`) together with a family of baths `β`, each of
dimension `d + 1` with vacuum `0` (arXiv:2610.05362, held version sha256 8f4637ef…, §2.3, p.12:
`ℋ_E := ⨂_{b} ℂ^{d_E}_b`, vacuum `|0⟩`, the other values the occupied sector). -/
abbrev OccSp (σ β : Type*) (d : ℕ) := σ × (β → Fin (d + 1))

/-- The number of baths of `F` that are occupied in the bath configuration `x`. -/
def nOcc {β : Type*} {d : ℕ} (F : Finset β) (x : β → Fin (d + 1)) : ℕ :=
  (F.filter fun b => x b ≠ 0).card

/-- The joint occupation projection `P_F := ∏_{b ∈ F} P_b`, `P_b := I − |0⟩⟨0|_b`
(arXiv:2610.05362, p.12 and Eq. (12), p.19). `P_∅ = I`. -/
noncomputable def projOcc {σ β : Type*} [DecidableEq σ] [Fintype β] [DecidableEq β] {d : ℕ}
    (F : Finset β) : Matrix (OccSp σ β d) (OccSp σ β d) ℂ :=
  open Classical in
  Matrix.diagonal fun p => if ∀ b ∈ F, p.2 b ≠ 0 then 1 else 0

/-- `z^{N_cat}` for the occupation operator `N_cat := Σ_{b ∈ B_cat} P_b` (Eq. (13), p.19); it is
diagonal in the bath basis with entry `z^{#occupied baths of B_cat}`. -/
noncomputable def zPowOcc {σ β : Type*} [DecidableEq σ] [Fintype β] [DecidableEq β] {d : ℕ}
    (Bcat : Finset β) (z : ℝ) : Matrix (OccSp σ β d) (OccSp σ β d) ℂ :=
  Matrix.diagonal fun p => ((z ^ nOcc Bcat p.2 : ℝ) : ℂ)

/-- `P_b z^{N_cat − P_b}` (Eq. (14), p.19): diagonal, entry `z^{#occupied baths of B_cat other
than b}` if bath `b` is occupied, else `0`. -/
noncomputable def projZPowOcc {σ β : Type*} [DecidableEq σ] [Fintype β] [DecidableEq β] {d : ℕ}
    (Bcat : Finset β) (b : β) (z : ℝ) : Matrix (OccSp σ β d) (OccSp σ β d) ℂ :=
  Matrix.diagonal fun p => if p.2 b ≠ 0 then ((z ^ nOcc (Bcat.erase b) p.2 : ℝ) : ℂ) else 0

/-- The vacuum initialization `E₀ψ := ψ ⊗ ⨂_b |0⟩_b` (p.12). -/
noncomputable def vacOcc {σ β : Type*} [DecidableEq σ] [Fintype β] [DecidableEq β] {d : ℕ} :
    Matrix (OccSp σ β d) σ ℂ :=
  vacIso (fun _ => (0 : Fin (d + 1)))

/-- Gate `U` *touches* bath `b`: it does not commute with the occupation projection `P_b`
(arXiv:2610.05362, Lemma 3.6, p.19).

**Formalization Note** A gate acting as the identity on bath `b` commutes with `P_b`; the lemma's
proof only uses `[P_b, U] = 0` for untouched baths, so "touches" is read as `[P_b, U] ≠ 0`. -/
def Touches {σ β : Type*} [Fintype σ] [DecidableEq σ] [Fintype β] [DecidableEq β] {d : ℕ}
    (U : Matrix (OccSp σ β d) (OccSp σ β d) ℂ) (b : β) : Prop :=
  projOcc {b} * U ≠ U * projOcc {b}

/-- The labelwise bound `a_b := Σ_{j : j touches b} ‖[P_b, U_j]‖` of a gate sequence
(arXiv:2610.05362, Lemma 3.6, p.19). -/
noncomputable def aBound {σ β : Type*} [Fintype σ] [DecidableEq σ] [Fintype β] [DecidableEq β]
    {d : ℕ} (Us : List (Matrix (OccSp σ β d) (OccSp σ β d) ℂ)) (b : β) : ℝ :=
  open Classical in
  (Us.map fun U =>
    if Touches U b then opNorm (projOcc {b} * U - U * projOcc {b}) else 0).sum

/-- The three occupation estimates of Lemma 3.6, Eqs. (12)–(14) (p.19), for a column
`Y : σ → OccSp`, a counted bath set `B_cat` and nonnegative bounds `a_b`:
(12) `‖P_F Y‖ ≤ ∏_{b∈F} a_b` for every `F ⊆ B_cat`;
(13) `Y† z^{N_cat} Y ⪯ ∏_{b ∈ B_cat} [1 + (z−1)a_b²] I` for every `z ≥ 1`;
(14) `Y† P_b z^{N_cat − P_b} Y ⪯ a_b² ∏_{c ∈ B_cat, c ≠ b} [1 + (z−1)a_c²] I` for every
`b ∈ B_cat` and `z ≥ 1`. -/
def OccBounds {σ β : Type*} [Fintype σ] [DecidableEq σ] [Fintype β] [DecidableEq β] {d : ℕ}
    (Bcat : Finset β) (a : β → ℝ) (Y : Matrix (OccSp σ β d) σ ℂ) : Prop :=
  (∀ F ⊆ Bcat, opNorm (projOcc (σ := σ) (d := d) F * Y) ≤ ∏ b ∈ F, a b) ∧
  (∀ z : ℝ, 1 ≤ z → LoewnerLE (Matrix.conjTranspose Y * zPowOcc (σ := σ) (d := d) Bcat z * Y)
    (((∏ b ∈ Bcat, (1 + (z - 1) * a b ^ 2) : ℝ) : ℂ) • (1 : Matrix σ σ ℂ))) ∧
  (∀ b ∈ Bcat, ∀ z : ℝ, 1 ≤ z → LoewnerLE (Matrix.conjTranspose Y * projZPowOcc (σ := σ) (d := d) Bcat b z * Y)
    (((a b ^ 2 * ∏ c ∈ Bcat.erase b, (1 + (z - 1) * a c ^ 2) : ℝ) : ℂ) • (1 : Matrix σ σ ℂ)))

/-- A system-only operator `U ⊗ I_baths`. -/
def sysOnly {σ β : Type*} [Fintype β] [DecidableEq β] {d : ℕ} (U : Matrix σ σ ℂ) :
    Matrix (OccSp σ β d) (OccSp σ β d) ℂ :=
  Matrix.of fun p q => if p.2 = q.2 then U p.1 q.1 else 0

/-- An operator on system ⊗ (bath `b`), extended by the identity on all other baths. -/
noncomputable def onBath {σ β : Type*} [Fintype β] [DecidableEq β] {d : ℕ} (b : β)
    (A : Matrix (σ × Fin (d + 1)) (σ × Fin (d + 1)) ℂ) : Matrix (OccSp σ β d) (OccSp σ β d) ℂ :=
  open Classical in
  Matrix.of fun p q => if ∀ c, c ≠ b → p.2 c = q.2 c then A (p.1, p.2 b) (q.1, q.2 b) else 0

/-- A normalized physical collision gate (arXiv:2610.05362, §3.3, p.19 and Lemma 3.6): a
Hamiltonian gate acting on the system only, or a forward/adjoint jump Cayley gate
`V_{J,h}^{±1}` on the system and one bath `b`, with duration `h` and strength `λ`. -/
inductive CollGate (σ β : Type*) (d : ℕ)
  | ham (U : Matrix σ σ ℂ)
  | jump (b : β) (J : Matrix (Fin d × σ) σ ℂ) (h lam : ℝ) (adj : Bool)

/-- The unitary of a collision gate on system ⊗ baths. -/
noncomputable def CollGate.mat {σ β : Type*} [Fintype σ] [DecidableEq σ] [Fintype β] [DecidableEq β]
    {d : ℕ} : CollGate σ β d → Matrix (OccSp σ β d) (OccSp σ β d) ℂ
  | .ham U => sysOnly U
  | .jump b J h _ adj => onBath b (if adj then (cayleyJ h J)ᴴ else cayleyJ h J)

end LindbladShallow


