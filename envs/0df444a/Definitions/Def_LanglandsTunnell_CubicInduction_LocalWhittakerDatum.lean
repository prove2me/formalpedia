-- Prove2me | Definitions.Def_LanglandsTunnell_CubicInduction_LocalWhittakerDatum
-- name    : LanglandsTunnell_CubicInduction_LocalWhittakerDatum
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/ae4bc5a7-65a9-5fa8-8cbb-86ee94cefb8c
-- title:
--   Local Whittaker datum for GL(3) at a finite place
-- statement:
--   Fix a finite place $v$ of $\mathbb{Q}$, i.e. a point of the height-one spectrum of $\mathcal{O}_{\mathbb{Q}}$, an additive character $\psi_v$ of the completion $\mathbb{Q}_v$ with values in $\mathbb{C}^\times$ (no condition on its conductor or nontriviality is imposed), and a function $W$ on $\mathrm{GL}_3(\mathbb{Q}_v)$ with complex values. The predicate `IsLocalWhittakerDatum` is the conjunction of six clauses. First, `IsGL3PsiWhittakerFn` for $\psi_v$: for all $x,y,z\in\mathbb{Q}_v$ and all $g$, one has $W(u(x,y,z)g)=\psi_v(x+y)W(g)$, where $u(x,y,z)$ is the upper triangular unipotent matrix with superdiagonal entries $x,y$ and corner entry $z$; thus the character is evaluated on the sum of the two superdiagonal entries, and for trivial $\psi_v$ the clause degenerates to left invariance under the full unipotent radical. Second, $W(1)=1$. Third, `HasWhittakerMultOne`: writing $V(W)$ for `gl3CyclicSubspace W`, the $\mathbb{C}$-span of all right translates $h\mapsto W(hg)$ of $W$ inside the space of all functions on $\mathrm{GL}_3(\mathbb{Q}_v)$, and letting $\mathrm{GL}_3(\mathbb{Q}_v)$ act on $V(W)$ by right translation (`gl3CyclicRep`), the space of linear functionals $L$ on $V(W)$ satisfying $L(\pi(u(x,y,z))f)=\psi_v(x+y)L(f)$ has rank at most $1$. Fourth, an irreducibility clause phrased in terms of these cyclic spans: every nonzero $F\in V(W)$ satisfies $W\in V(F)$. Fifth, smoothness in the form of an open subgroup $U_v\le \mathrm{GL}_3(\mathbb{Q}_v)$ with $W(gk)=W(g)$ for all $k\in U_v$ and all $g$. Sixth, admissibility: for every open subgroup $U_v$ there is a finite set $B$ of complex-valued functions on $\mathrm{GL}_3(\mathbb{Q}_v)$ such that every $F\in V(W)$ which is right $U_v$-invariant lies in the $\mathbb{C}$-span of $B$ (the members of $B$ are not themselves required to lie in $V(W)$).
--
--   **Relation to Mathlib.** Mathlib has no notion of Whittaker functions, Whittaker functionals or admissible smooth representations of $p$-adic groups; these are the project's own definitions, formulated using Mathlib's `AddChar`, general linear groups over adic completions, and `Submodule.span`.
--
--   **Where it is used.** The predicate pins down the local components at finite places of the Whittaker function of the $\mathrm{GL}_3/\mathbb{Q}$ automorphic form produced by cubic induction, in the Langlands–Tunnell input to the modularity of the mod $3$ representation attached to a Frey curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LanglandsTunnell_CubicInduction_LocalWhittakerDatum.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField

namespace LanglandsTunnell.CubicInduction

def IsLocalWhittakerDatum (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ)
    (W : LocalGL3 v → ℂ) : Prop :=
  IsGL3PsiWhittakerFn ψv W ∧ W 1 = 1 ∧
    HasWhittakerMultOne ψv W ∧
    (∀ F ∈ gl3CyclicSubspace W, F ≠ 0 → W ∈ gl3CyclicSubspace F) ∧
    (∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g) ∧
    ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
      ∃ B : Finset (LocalGL3 v → ℂ), ∀ F ∈ gl3CyclicSubspace W,
        (∀ k ∈ Uv, ∀ g : LocalGL3 v, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ))

end LanglandsTunnell.CubicInduction

end


