-- Prove2me | Definitions.Def_LowAccLTC_IsFacesCoboundaryExpander
-- name    : LowAccLTC_IsFacesCoboundaryExpander
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:39:24.5843+00:00
-- url     : https://prove2.me/theorems/8e61bdf7-9fbd-47ef-a6d3-e8426adde6cb
-- title:
--   $(m,\beta)$-coboundary expansion of the $j$-faces complex $\mathcal F^jX$
-- statement:
--   Let $Y=\mathcal F^jX$ be the $j$-faces complex of a weighted partite complex $X$: its vertices are the $j$-faces of $X$, and $k$ pairwise disjoint $j$-faces form a face iff their union is a face of $X$; oriented edges and triangles are sampled by sampling a $2j$- or $3j$-face of $X$ from the induced measure and partitioning it uniformly into ordered parts. For $\phi:\vec Y\langle 2\rangle\to\mathrm{Sym}(m)$ antisymmetric ($\phi(vu)=\phi(uv)^{-1}$) and $\psi:Y\langle 1\rangle\to\mathrm{Sym}(m)$ write $\delta\psi(uv)=\psi(v)\psi(u)^{-1}$. $Y$ is an **$(m,\beta)$-coboundary expander** if for every antisymmetric $\phi$ there is $\psi$ with
--   $$\beta\cdot\Pr_{uv\in\vec Y\langle 2\rangle}\big[\phi(uv)\neq\delta\psi(uv)\big]\ \le\ \Pr_{uvw\in\vec Y\langle 3\rangle}\big[\phi(wu)\phi(vw)\phi(uv)\neq \mathrm{Id}\big].$$
--
--   This is assumption 2 of Theorem 4.1, supplied for KMS complexes by Theorem 2.40.
--
--   **Formalization Note** $\mathrm{Sym}(m)$ is `Equiv.Perm (Fin m)`, whose product is composition from right to left, as in the paper.
-- source:
--   Ben Yaacov, Dikstein, Liu, Randomness-Efficient Robust LTCs in the Low-Acceptance Regime from HDXs (manuscript, sha256 04242e17…), Definition 2.14 p.17 (PDF p.20), Definition 2.32 p.21 (PDF p.24)

import Definitions.Def_LowAccLTC_IsJAgreementTestable

namespace LowAccLTC

/-! Ben Yaacov, Dikstein, Liu, *Randomness-Efficient Robust LTCs in the Low-Acceptance Regime from HDXs*,
unpublished manuscript (sha256 04242e17…); page references are printed pages (PDF page − 3). -/

namespace PartiteComplex

variable {r : ℕ} {V T : Type*} [Fintype T] (X : PartiteComplex r V T)

/-- `(u, v)` is an oriented edge of the `j`-faces complex `F^j X` (Definition 2.14, p.17):
`u, v` are disjoint `j`-faces whose union is a face. -/
def IsYEdge (j : ℕ) (u v : Finset V) : Prop := by
  classical exact u.card = j ∧ v.card = j ∧ Disjoint u v ∧ X.IsFace (u ∪ v)

/-- The `j`-faces complex `Y = F^j X` is an `(m, β)`-coboundary expander (Definition 2.32,
p.21): for every antisymmetric `ϕ : Y⃗⟨2⟩ → Sym(m)` there is `ψ : Y⟨1⟩ → Sym(m)` with
`β · P_{uv ∈ Y⃗⟨2⟩}[ϕ(uv) ≠ δψ(uv)] ≤ P_{uvw ∈ Y⃗⟨3⟩}[ϕ(wu)ϕ(vw)ϕ(uv) ≠ Id]`, where
`δψ(uv) = ψ(v)ψ(u)⁻¹`. Oriented edges and triangles of `Y` are sampled from the measure induced
by `μ` (Definition 2.14: sample a `2j`- resp. `3j`-face and partition it uniformly; the order
of the parts is uniform).

**Formalization Note.** `Sym(m)` is `Equiv.Perm (Fin m)`, whose multiplication is composition
(right to left, as in the paper). `ϕ` and `ψ` are total functions; only their values on
oriented edges and on `j`-faces matter. -/
def IsFacesCoboundaryExpander (j m : ℕ) (β : ℝ) : Prop :=
  ∀ ϕ : Finset V → Finset V → Equiv.Perm (Fin m),
    (∀ u v, X.IsYEdge j u v → ϕ u v = (ϕ v u)⁻¹) →
    ∃ ψ : Finset V → Equiv.Perm (Fin m),
      β * X.E (fun t => avg (jPairs r j) (fun P =>
          ind (ϕ (X.face t P.1) (X.face t P.2) ≠ ψ (X.face t P.2) * (ψ (X.face t P.1))⁻¹)))
        ≤ X.E (fun t => avg (jTriples r j) (fun Q =>
          ind (ϕ (X.face t Q.2.2) (X.face t Q.1) * ϕ (X.face t Q.2.1) (X.face t Q.2.2) *
            ϕ (X.face t Q.1) (X.face t Q.2.1) ≠ 1)))

end PartiteComplex

end LowAccLTC


