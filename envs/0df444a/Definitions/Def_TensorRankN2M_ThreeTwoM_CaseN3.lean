-- Prove2me | Definitions.Def_TensorRankN2M_ThreeTwoM_CaseN3
-- name    : TensorRankN2M_ThreeTwoM_CaseN3
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T04:18:00.908987+00:00
-- url     : https://prove2.me/theorems/eee4ef44-e363-4e29-ab10-0f2390ce1b4f
-- title:
--   The case n = 3 (§4.1): Δ = 2rk(H) − rk(L), N = ker(H) ⊆ U, S = {x ∈ N : f_1(x), f_2(x) ∈ f_0(N)}
-- statement:
--   Fix an $R$-rank decomposition of $\langle 3,2,m\rangle$ with the maps $f_i$, $J$, $L$, $H$ of §4 (now $n=3$, indices $1,2$). The space $U^{\wedge 2}$ of alternating $2\times 2$ arrays over $U$ is identified with $U$ by
--   $$x\mapsto c,\qquad c_{1,2}=-x,\quad c_{2,1}=x,\quad c_{1,1}=c_{2,2}=0,$$
--   under which $h(x)=(-f_2(x),f_1(x))$. Define
--   $$\Delta=2\operatorname{rk}(H)-\operatorname{rk}(L)\in\mathbb Z,\qquad N=\ker(H)\subseteq U,\qquad S=\{x\in N: f_1(x),f_2(x)\in f_0(N)\}.$$
--   Then $N=\ker(f_1+J)\cap\ker(f_2+J)$, and $S$ is a subspace of $N$.
--
--   These are the quantities of the refined $n=3$ count that improves $R\ge 24m/5$ to $R\ge(24m+2)/5$ (Lemma 12).
--
--   **Formalization Note.** `skewOfU 𝔽 m : U →ₗ U^{∧2}` is the identification above (`skewCoef i j` is $-1$ if $i<j$, $1$ if $j<i$, $0$ on the diagonal). `Nspace d` is the kernel of $H\circ$`skewOfU`, a submodule of $U$; `Sspace d` is $N\cap f_1^{-1}(f_0(N))\cap f_2^{-1}(f_0(N))$ inside $U$; `Delta d : ℤ`. The names `Nspace`, `Sspace` keep these apart from the change-of-basis matrix $S$ (p. 3) and the subspace $S$ of Lemma 8.
-- source:
--   Jason Yang, New lower bounds on tensor rank of (n,2,m) matrix multiplication with GPT-6 Astra, STOC 2027 submission (manuscript of October 2026, sha256 6c1df229…), p. 6, §4.1

import Mathlib
import Definitions.Def_TensorRankN2M_ThreeTwoM_Decomposition
import Definitions.Def_TensorRankN2M_ThreeTwoM_Normalization
import Definitions.Def_TensorRankN2M_ThreeTwoM_SkewAugmentation
import Definitions.Def_TensorRankN2M_ThreeTwoM_N2M

/-!
# The case n = 3 (§4.1): Δ, N and S

Jason Yang, *New lower bounds on tensor rank of (n,2,m) matrix multiplication with GPT-6 Astra*,
STOC 2027 submission (manuscript of October 2026), p. 6, §4.1.

For a decomposition of ⟨3,2,m⟩:
* `Delta d = 2 rk(H) − rk(L)`, an integer;
* `skewOfU : U ≅ U^{∧2}`, `x ↦ c` with `c_{1,2} = −x`, `c_{2,1} = x`, `c_{1,1} = c_{2,2} = 0`,
  under which `h(x) = (−f_2(x), f_1(x))` as on p. 6;
* `Nspace d = ker(H) ⊆ U`, the kernel of `H` transported to `U` along `skewOfU`;
* `Sspace d = {x ∈ N : f_1(x), f_2(x) ∈ f_0(N)}`.
The Lean names `Nspace`, `Sspace` keep these apart from the change-of-basis matrix `S` (p. 3)
and the subspace `S` of Lemma 8.
-/

namespace TensorRankN2M.ThreeTwoM

/-- Coefficients of the isomorphism `U ≅ U^{∧2}`: `c_{i,j} = skewCoef i j • x`, i.e.
`c_{1,2} = −x`, `c_{2,1} = x`, and `0` on the diagonal. -/
def skewCoef {𝔽 : Type*} [Field 𝔽] (i j : Idx 3) : 𝔽 :=
  if i.1 < j.1 then -1 else if j.1 < i.1 then 1 else 0

/-- The isomorphism `U ≅ U^{∧2}` of p. 6: `x ↦ c` with `c_{1,2} = −x`, `c_{2,1} = x`. -/
def skewOfU (𝔽 : Type*) [Field 𝔽] (m : ℕ) : U 𝔽 m →ₗ[𝔽] SkewArrays 𝔽 (U 𝔽 m) (Idx 3) :=
  LinearMap.codRestrict _
    (LinearMap.pi fun i => LinearMap.pi fun j => (skewCoef i j : 𝔽) • LinearMap.id)
    (fun x => by
      refine ⟨fun i => by simp [skewCoef], fun i j => ?_⟩
      rcases lt_trichotomy i.1 j.1 with hij | hij | hij
      · have h1 : i < j := hij
        simp [skewCoef, h1, not_lt_of_gt h1]
      · have : i = j := Subtype.ext hij
        subst this
        simp [skewCoef]
      · have h1 : j < i := hij
        simp [skewCoef, h1, not_lt_of_gt h1])

namespace Decomposition

variable {𝔽 : Type*} [Field 𝔽] {m R : ℕ} (d : Decomposition 𝔽 3 2 m R)

/-- `Δ = 2 rk(H) − rk(L)` (p. 6), in `ℤ`. -/
noncomputable def Delta : ℤ :=
  2 * (Module.finrank 𝔽 (LinearMap.range d.H) : ℤ) - Module.finrank 𝔽 (LinearMap.range d.L)

/-- `N = ker(H) ⊆ U` (p. 6), via `U ≅ U^{∧2}`. -/
def Nspace : Submodule 𝔽 (U 𝔽 m) :=
  LinearMap.ker (d.H ∘ₗ skewOfU 𝔽 m)

/-- `S = {x ∈ N : f_1(x), f_2(x) ∈ f_0(N)}` (p. 6). -/
def Sspace : Submodule 𝔽 (U 𝔽 m) :=
  d.Nspace ⊓ (d.Nspace.map (d.f 0 ∘ₗ (U 𝔽 m).subtype)).comap (d.f 1 ∘ₗ (U 𝔽 m).subtype) ⊓
    (d.Nspace.map (d.f 0 ∘ₗ (U 𝔽 m).subtype)).comap (d.f 2 ∘ₗ (U 𝔽 m).subtype)

end Decomposition

end TensorRankN2M.ThreeTwoM


