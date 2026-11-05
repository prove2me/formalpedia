-- Prove2me | Definitions.Def_BindingEntChannels_filterLeft
-- name    : BindingEntChannels_filterLeft
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:38:24.958618+00:00
-- url     : https://prove2.me/theorems/6fcbb724-a32a-4dca-ac67-c509c0183eaa
-- title:
--   Local CP filter $\Gamma\otimes I$ on Alice's side
-- statement:
--   Let $\Gamma(X)=\sum_{j=1}^r G_jXG_j^\dagger$ be a completely positive map from operators on $\mathbb C^I$ to operators on $\mathbb C^K$, given by a finite family of Kraus operators $G_j$, **not necessarily trace preserving**. For an operator $\tau$ on $\mathbb C^I\otimes\mathbb C^J$,
--
--   $$
--   (\Gamma\otimes I)\,\tau=\sum_{j=1}^r (G_j\otimes 1)\,\tau\,(G_j\otimes 1)^\dagger ,
--   $$
--
--   an operator on $\mathbb C^K\otimes\mathbb C^J$.
--
--   The proof of the Theorem writes every state as such a filter applied to a singlet, and uses that such a local action cannot create free entanglement or entanglement.
--
--   **Formalization Note** No completeness condition $\sum_j G_j^\dagger G_j=1$ is imposed, as the paper says "Γ is CP, but not necessarily trace-preserving map". $\Gamma$ acts on the first (Alice's) factor.
-- source:
--   Horodecki, Horodecki, Horodecki, Binding entanglement channels, arXiv:quant-ph/9904092v1, §II, p. 2 (proof of the Theorem)

import Mathlib

open scoped Matrix

namespace BindingEntChannels

/-- Horodecki, Horodecki, Horodecki, *Binding entanglement channels*, arXiv:quant-ph/9904092v1,
§II, p. 2: the local operation `Γ ⊗ I`, where "Γ is CP, but not necessarily trace-preserving
map", applied to a bipartite operator `τ` on `I × J`:
`(Γ ⊗ I)τ = Σ_j (G_j ⊗ 1) τ (G_j ⊗ 1)†`, with `Γ(X) = Σ_j G_j X G_j†`.

**Formalization Note.** The CP map `Γ : M_I → M_K` is given by a finite Kraus family
`G : Fin r → Matrix K I ℂ`, with no completeness condition `Σ G_j†G_j = 1`, as the paper allows
non-trace-preserving `Γ`. It acts on the first (Alice's) factor; the output is on `K × J`. -/
noncomputable def filterLeft {I J K : Type*} [Fintype I] [Fintype J] [DecidableEq J] {r : ℕ}
    (G : Fin r → Matrix K I ℂ) (τ : Matrix (I × J) (I × J) ℂ) : Matrix (K × J) (K × J) ℂ :=
  ∑ j, Matrix.kronecker (G j) (1 : Matrix J J ℂ) * τ * (Matrix.kronecker (G j) (1 : Matrix J J ℂ))ᴴ

end BindingEntChannels


