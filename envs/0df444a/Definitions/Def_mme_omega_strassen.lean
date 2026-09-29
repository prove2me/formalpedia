-- Prove2me | Definitions.Def_mme_omega_strassen
-- name    : mme_omega_strassen
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-05-28T03:36:00.398258+00:00
-- url     : https://prove2.me/theorems/d43bcfb7-8cf1-4507-baa9-647e85353a01
-- statement:
--   Defines the **matrix-multiplication exponent** $\omega$ via Strassen's **restriction preorder** — the equivalent formulation underlying the asymptotic-spectrum theory (Wigderson–Zuiddam, Def. 2.4–2.5).
--
--   For tensors $T_1, T_2$ (possibly in different ambient spaces), `Restrict T₁ T₂` holds when independent linear maps on each tensor leg send $T_2$ to $T_1$; this is a Strassen preorder $T_1 \le T_2$. Writing $I_r$ for the diagonal unit tensor $\sum_{j=1}^r e_j\otimes\cdots\otimes e_j$ (`diagTensor d r`), the **restriction rank** is $R(T) = \min\{\, r : T \le I_r \,\}$ (`strassenRank`), and
--
--   $$\omega_{\mathrm{Strassen}} := \inf_{n\ge 2} \frac{\log R(\langle n,n,n\rangle)}{\log n}.$$
--
--   This rank coincides with the textbook tensor rank of `mme_omega`; their equality is the content of the child theorem `mme_omega_eq_strassen`. Imports `Definitions.Def_mme_omega` for `MMTensor`.
-- source:
--   https://www.math.ias.edu/~avi/PUBLICATIONS/WigdersonZu_Final_Draft_Oct2023.pdf

import Mathlib.LinearAlgebra.PiTensorProduct
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Lattice
import Definitions.Def_mme_omega

universe u

open PiTensorProduct BigOperators

namespace MME

variable {K : Type u} [Field K]

/-! ## Tensor restriction (Strassen's preorder)

`Restrict T₁ T₂` means: there exist linear maps `f_i : W i → V i` such that
the induced map `⨂ f_i : ⨂ W i → ⨂ V i` sends `T₂` to `T₁`.

This is the natural notion of "T₁ is at most T₂" in Strassen's framework:
T₁ is a restriction of T₂ along d independent linear maps. -/

def Restrict
    {d : ℕ} {V W : Fin d → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (T₁ : PiTensorProduct K V)
    (T₂ : PiTensorProduct K W) : Prop :=
  ∃ f : ∀ i, W i →ₗ[K] V i, PiTensorProduct.map f T₂ = T₁

/-! ## The diagonal tensor of size r

The constant `r : Tensor K d` in Strassen's framework: an order-d tensor in
`(Fin r → K)^d` whose value is `∑_{j=1}^r e_j ⊗ … ⊗ e_j`.

By `Restrict T (diagTensor d r) ↔ ∃ r-term decomposition T = ∑ u_i ⊗ … ⊗ w_i`,
this provides the bridge between Strassen's `T ≤ r` and textbook rank ≤ r. -/

noncomputable def diagTensor (K : Type u) [Field K] (d r : ℕ) :
    PiTensorProduct K (fun (_ : Fin d) => Fin r → K) :=
  ∑ j : Fin r, tprod K (fun _ => (Pi.single j 1 : Fin r → K))

/-! ## Strassen-style tensor rank

`strassenRank T` is the smallest `r` such that `T ≤ diagTensor d r` in the
Restrict preorder. Equivalent to `tensorRank T`; that equivalence is the
content of child theorem `mme_omega_eq_strassen` at this layer. -/

noncomputable def strassenRank
    {d : ℕ} {V : Fin d → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    (T : PiTensorProduct K V) : ℕ :=
  sInf { r | Restrict T (diagTensor K d r) }

/-! ## The matrix-multiplication exponent ω (Strassen form)

Same shape as `matMulExp`, but built from `strassenRank` instead of
`tensorRank`. -/

noncomputable def matMulExp_strassen (K : Type u) [Field K] : ℝ :=
  iInf (fun n : ℕ =>
    if 1 < n then
      Real.log (strassenRank (MMTensor K n n n) : ℝ) / Real.log n
    else 3)

end MME


