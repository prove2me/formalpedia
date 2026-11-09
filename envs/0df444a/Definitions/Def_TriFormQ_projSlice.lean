-- Prove2me | Definitions.Def_TriFormQ_projSlice
-- name    : TriFormQ_projSlice
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:47:15.793746+00:00
-- url     : https://prove2.me/theorems/7796c72d-8109-4f39-88d9-12502788974a
-- title:
--   Projected slice $\tilde f\langle v\rangle$
-- statement:
--   Let $f$ be a trilinear form on $\mathbb F_q^n$ and let $w_1,\dots,w_e\in\mathbb F_q^n$ be probe vectors, defining the projection $\Pi:\lambda\mapsto(\lambda(w_1),\dots,\lambda(w_e))$ of covectors. For $v\in\mathbb F_q^n$ the **projected slice** $\tilde f\langle v\rangle=\Pi\circ f\langle v\rangle$ is the linear map
--
--   $$u\ \mapsto\ \big(f(u,v,w_1),\dots,f(u,v,w_e)\big),$$
--
--   represented by the $e\times n$ matrix whose $j$-th row is the linear functional $u\mapsto f(u,v,w_j)$, with entries $\sum_k f\langle v\rangle_{ik}(w_j)_k$.
-- source:
--   Grigorescu–Juba–Wimmer–Xie, Optimal Quantum Query Bounds for Identifying Classes of 3-Tensors, STOC 2027 submission (manuscript sha256 c56b0365…), Eqs. (15)–(16), p.26 (PDF p.29)

import Definitions.Def_TriFormQ_sliceV

namespace TriFormQ

/-- Grigorescu–Juba–Wimmer–Xie, *Optimal Quantum Query Bounds for Identifying Classes of
3-Tensors*, STOC 2027 submission (manuscript sha256 c56b0365…), Eqs. (15)–(16), p.26 (PDF p.29):
for probe vectors `w₁, …, w_e ∈ W`, "Π : W* → 𝔽_q^e, λ ↦ (λ(w₁), …, λ(w_e))" and
"f̃⟨v⟩ := Π ∘ f⟨v⟩ : U → 𝔽_q^e, f̃⟨v⟩(u) = (f(u, v, w₁), …, f(u, v, w_e))". "The map f̃⟨v⟩ is
represented by an e × n matrix. Its jth row is the linear functional u ↦ f(u, v, w_j)."

**Formalization Note.** `ws : Fin e → Vec F n` lists the probe vectors `w₁, …, w_e`; entry
`(j, i)` of the matrix is `f(e_i, v, w_j) = Σ_k f⟨v⟩_{ik} (w_j)_k`. -/
def projSlice {F : Type} [Field F] {n e : ℕ} (θ : TriForm F n) (ws : Fin e → Vec F n)
    (v : Vec F n) : Matrix (Fin e) (Fin n) F :=
  Matrix.of fun j i => ∑ k, sliceV θ v i k * ws j k

end TriFormQ


