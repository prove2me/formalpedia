-- Prove2me | Definitions.Def_ChapterCarlemanUnboundedHop
-- name    : ChapterCarlemanUnboundedHop
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-03T18:43:08.850469+00:00
-- url     : https://prove2.me/theorems/becbc63c-252b-45a9-929d-15785b923ab2
-- title:
--   The Lean 4 theorem `kernelFun_eq_sum` in the `?` chapter of the timepiece formalization
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterCarlemanUnboundedHop.lean`): generated def bundle for ChapterCarlemanUnboundedHop. See BookProof/ChapterCarlemanUnboundedHop.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterCarlemanUnboundedHop.lean

import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterStoneBridge
import Mathlib


/-!
# A flux (Carleman) criterion for lattice operators with **unbounded hops**

Placeholder header; filled in once the mathematics is in place.
-/

namespace BookProof.CarlemanUnboundedHop

open Finset

noncomputable section

/-! ## 1. The kernel, the recursion and the flux across a cut -/

/-- A Hermitian matrix kernel on the lattice `ℕ`. -/
def IsHermitianKernel (a : ℕ → ℕ → ℂ) : Prop :=
  ∀ n k, a k n = (starRingEnd ℂ) (a n k)

/-- The deficiency recursion `∑ₖ a n k u k = z uₙ` for a kernel with (absolutely)
convergent rows. -/
structure LadderRecInf (a : ℕ → ℕ → ℂ) (u : ℕ → ℂ) (z : ℂ) : Prop where
  row : ∀ n, Summable fun k => a n k * u k
  eqn : ∀ n, ∑' k, a n k * u k = z * u n

/-- The **flux** of `u` through the cut separating `{0, …, N}` from `{N+1, …}`. -/
def flux (a : ℕ → ℕ → ℂ) (u : ℕ → ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ range (N + 1),
    (starRingEnd ℂ) (u n) * ∑' i : ℕ, a n (i + (N + 1)) * u (i + (N + 1))







/-! ## 2. The flux bound for a kernel with decaying hops -/

section Bound

variable {a : ℕ → ℕ → ℂ} {u : ℕ → ℂ} {A θ Θ : ℕ → ℝ}

/-- The boundary mass carried by the cut at `N`: the `ℓ²`-mass on either side of the
cut, weighted by the tail `Θ` of the hop profile. -/
def cutMass (u : ℕ → ℂ) (Θ : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ range (N + 1), Θ (N - n) * ‖u n‖ ^ 2 + ∑' i : ℕ, Θ i * ‖u (i + (N + 1))‖ ^ 2











/-! ## 3. Carleman's condition: the flux is small along a subsequence of cuts -/









end Bound

/-! ## 4. The kernel operator on `ℓ²(ℕ)` -/

section Operator

open BookProof BookProof.NavierStokesFlow BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine

/-- A Hermitian kernel whose columns are square-summable: enough for the associated
matrix to act on the finitely supported states. -/
structure IsL2Kernel (a : ℕ → ℕ → ℂ) : Prop where
  herm : IsHermitianKernel a
  col : ∀ k, Memℓp (fun n => a n k) 2

/-- The action of the kernel on a coefficient sequence. -/
def kernelFun (a : ℕ → ℕ → ℂ) (f : ℕ → ℂ) : ℕ → ℂ := fun n => ∑' k : ℕ, a n k * f k

theorem kernelFun_eq_sum (a : ℕ → ℕ → ℂ) {f : ℕ → ℂ} {M : ℕ} (hf : ∀ n, M ≤ n → f n = 0)
    (n : ℕ) : kernelFun a f n = ∑ k ∈ range M, a n k * f k := by
  refine tsum_eq_sum ?_
  intro k hk
  rw [hf k (by simpa using hk)]
  ring

theorem memℓp_finsetSum (s : Finset ℕ) (g : ℕ → ℕ → ℂ) (h : ∀ k ∈ s, Memℓp (g k) 2) :
    Memℓp (fun n => ∑ k ∈ s, g k n) 2 := by
  classical
  induction s using Finset.induction with
  | empty => exact zero_memℓp (E := fun _ : ℕ => ℂ) (p := 2)
  | insert j s hj ih =>
    have h1 : Memℓp (g j) 2 := h j (Finset.mem_insert_self _ _)
    have h2 : Memℓp (fun n => ∑ k ∈ s, g k n) 2 :=
      ih fun k hk => h k (Finset.mem_insert_of_mem hk)
    have heq : (fun n => ∑ k ∈ insert j s, g k n) = g j + (fun n => ∑ k ∈ s, g k n) := by
      funext n
      simp [Finset.sum_insert hj]
    rw [heq]
    exact h1.add h2

theorem memℓp_kernelFun {a : ℕ → ℕ → ℂ} (hk : IsL2Kernel a) {f : ℕ → ℂ} {M : ℕ}
    (hf : ∀ n, M ≤ n → f n = 0) : Memℓp (kernelFun a f) 2 := by
  have heq : kernelFun a f = fun n => ∑ k ∈ range M, f k * a n k := by
    funext n
    rw [kernelFun_eq_sum a hf n]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [heq]
  exact memℓp_finsetSum (range M) (fun k n => f k * a n k)
    fun k _ => (hk.col k).const_smul (f k)

/-- The operator defined by an `ℓ²`-column Hermitian kernel, on the finitely supported
states of `ℓ²(ℕ)`. -/
def kernelOp {a : ℕ → ℕ → ℂ} (hk : IsL2Kernel a) : lpFiniteModes ℕ →ₗ[ℂ] L2N where
  toFun f := ⟨kernelFun a ((f : L2N) : ℕ → ℂ),
    memℓp_kernelFun hk (Classical.choose_spec (exists_tail_zero f.2))⟩
  map_add' f g := by
    obtain ⟨Mf, hMf⟩ := exists_tail_zero f.2
    obtain ⟨Mg, hMg⟩ := exists_tail_zero g.2
    have hf : ∀ n, max Mf Mg ≤ n → ((f : L2N) : ℕ → ℂ) n = 0 :=
      fun n hn => hMf n (le_trans (le_max_left _ _) hn)
    have hg : ∀ n, max Mf Mg ≤ n → ((g : L2N) : ℕ → ℂ) n = 0 :=
      fun n hn => hMg n (le_trans (le_max_right _ _) hn)
    have hfg : ∀ n, max Mf Mg ≤ n → (((f + g : lpFiniteModes ℕ) : L2N) : ℕ → ℂ) n = 0 := by
      intro n hn
      simp [hf n hn, hg n hn]
    ext n
    change kernelFun a (((f + g : lpFiniteModes ℕ) : L2N) : ℕ → ℂ) n = _
    rw [kernelFun_eq_sum a hfg n]
    change _ = kernelFun a ((f : L2N) : ℕ → ℂ) n + kernelFun a ((g : L2N) : ℕ → ℂ) n
    rw [kernelFun_eq_sum a hf n, kernelFun_eq_sum a hg n, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have : (((f + g : lpFiniteModes ℕ) : L2N) : ℕ → ℂ) k
        = ((f : L2N) : ℕ → ℂ) k + ((g : L2N) : ℕ → ℂ) k := by simp
    rw [this]; ring
  map_smul' c f := by
    obtain ⟨Mf, hMf⟩ := exists_tail_zero f.2
    have hcf : ∀ n, Mf ≤ n → (((c • f : lpFiniteModes ℕ) : L2N) : ℕ → ℂ) n = 0 := by
      intro n hn
      simp [hMf n hn]
    ext n
    change kernelFun a (((c • f : lpFiniteModes ℕ) : L2N) : ℕ → ℂ) n = _
    rw [kernelFun_eq_sum a hcf n]
    change _ = c * kernelFun a ((f : L2N) : ℕ → ℂ) n
    rw [kernelFun_eq_sum a hMf n, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have : (((c • f : lpFiniteModes ℕ) : L2N) : ℕ → ℂ) k = c * ((f : L2N) : ℕ → ℂ) k := by simp
    rw [this]; ring

@[simp] theorem kernelOp_coe {a : ℕ → ℕ → ℂ} (hk : IsL2Kernel a) (f : lpFiniteModes ℕ) :
    ((kernelOp hk f : L2N) : ℕ → ℂ) = kernelFun a ((f : L2N) : ℕ → ℂ) := rfl















end Operator

/-! ## 5. An instance with genuinely unbounded hops -/

section Instance

open BookProof BookProof.NavierStokesFlow BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine

/-- A Hermitian matrix on `ℓ²(ℕ)` with **infinite hop range**: the entry at distance `r`
from the diagonal is `(1 + min n k) ρ^r`, and the diagonal is an arbitrary real sequence
`b` — no growth restriction on it whatsoever. -/
def geoHop (b : ℕ → ℝ) (rho : ℝ) : ℕ → ℕ → ℂ := fun n k =>
  if n = k then ((b n : ℝ) : ℂ)
  else (((1 + ((min n k : ℕ) : ℝ)) * rho ^ (max n k - min n k) : ℝ) : ℂ)





















end Instance

end

end BookProof.CarlemanUnboundedHop


