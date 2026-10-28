-- Prove2me | Definitions.Def_WildeQIT_diamondNorm
-- name    : WildeQIT_diamondNorm
-- status  : Definition
-- author  : @nonlocally
-- created : 2026-09-07T05:40:47.229186+00:00
-- url     : https://prove2.me/theorems/93a5c780-b040-427a-bab1-fb81266bbf49
-- title:
--   Diamond-norm distance $\|\mathcal{N} - \mathcal{M}\|_\diamond$ between quantum channels (and $\mathrm{id}_R \otimes \mathcal{N}$)
-- statement:
--   **Definition 9.1.3 (Diamond-Norm Distance).** Let $\mathcal{N}, \mathcal{M} : \mathcal{L}(\mathcal{H}_A) \to \mathcal{L}(\mathcal{H}_B)$ be quantum channels. The diamond-norm distance is defined as
--
--   $$
--   \|\mathcal{N} - \mathcal{M}\|_\diamond \equiv \sup_{n} \max_{\rho_{R_n A}} \left\| (\mathrm{id}_{R_n} \otimes \mathcal{N}_{A \to B})(\rho_{R_n A}) - (\mathrm{id}_{R_n} \otimes \mathcal{M}_{A \to B})(\rho_{R_n A}) \right\|_1 ,
--   $$
--
--   where $\rho_{R_n A} \in \mathcal{D}(\mathcal{H}_{R_n} \otimes \mathcal{H}_A)$ and $R_n$ is a reference system of dimension $n$.
--
--   The diamond norm quantifies how well two channels can be distinguished by any strategy that may use entanglement with a reference system; Theorem 9.1.1 shows the supremum is attained by a pure state with $\dim \mathcal{H}_R = \dim \mathcal{H}_A$.
--
--   **Formalization Note.** Channels are Kraus representations `N M : WildeQIT.QChannel a b`. The file first defines `WildeQIT.QChannel.tensorIdApply r N X = ∑ i, (1 ⊗ₖ N.K i) * X * (1 ⊗ₖ N.K i)ᴴ`, the action of $\mathrm{id}_R \otimes \mathcal{N}$ on `X : Matrix (r × a) (r × a) ℂ` (Kronecker convention, reference system first). Then `WildeQIT.diamondNorm N M` is the real supremum `sSup` of the set of trace distances `traceDist (N.tensorIdApply (Fin n) ρ) (M.tensorIdApply (Fin n) ρ)` over all `n : ℕ` and all density operators `ρ` on `Fin n × a`. Mathlib's `sSup` returns 0 for an empty or unbounded set; the set is nonempty whenever `a` is nonempty (take $n = 1$) and is bounded by 2 (both arguments are density operators), so no junk value arises in that case. It is a supremum over the union over $n$, which coincides with $\sup_n \max_\rho$.
-- source:
--   Wilde, *Quantum Information Theory*, 2nd ed. (Cambridge University Press, 2017; arXiv:1106.1445v8), §9.1.6 "Channel Distinguishability and the Diamond Norm", Definition 9.1.3 (Diamond-Norm Distance).

import Definitions.Def_WildeQIT_traceDist
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_QChannel
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
Wilde, *Quantum Information Theory* (2nd ed.), §9.1.6, Definition 9.1.3 (Diamond-Norm Distance).

Let `𝒩, ℳ : L(ℋ_A) → L(ℋ_B)` be quantum channels. The diamond-norm distance is
`‖𝒩 − ℳ‖_◇ ≡ sup_n max_{ρ_{R_n A}} ‖(id_{R_n} ⊗ 𝒩_{A→B})(ρ_{R_n A}) − (id_{R_n} ⊗ ℳ_{A→B})(ρ_{R_n A})‖₁`,
where `ρ_{R_n A} ∈ 𝒟(ℋ_{R_n} ⊗ ℋ_A)` and `R_n` is a reference system of dimension `n`.
-/

open Matrix
open Kronecker

namespace WildeQIT

/-- The channel `id_R ⊗ 𝒩` acting on operators of the composite system `R ⊗ A`, for a channel
`𝒩 : L(ℋ_A) → L(ℋ_B)` in Kraus form: `(id_R ⊗ 𝒩)(X) = ∑ᵢ (I_R ⊗ Kᵢ) X (I_R ⊗ Kᵢ)†`. -/
def QChannel.tensorIdApply {a b : Type} [Fintype a] [Fintype b] [DecidableEq a]
    (r : Type) [Fintype r] [DecidableEq r] (N : QChannel a b)
    (X : Matrix (r × a) (r × a) ℂ) : Matrix (r × b) (r × b) ℂ :=
  ∑ i, ((1 : Matrix r r ℂ) ⊗ₖ N.K i) * X * ((1 : Matrix r r ℂ) ⊗ₖ N.K i)ᴴ

/-- **Definition 9.1.3 (Diamond-Norm Distance).** For channels `𝒩, ℳ : L(ℋ_A) → L(ℋ_B)`,
`‖𝒩 − ℳ‖_◇` is the supremum, over all reference-system dimensions `n` and all density
operators `ρ` on `R_n ⊗ A` (`R_n` indexed by `Fin n`), of the trace distance
`‖(id ⊗ 𝒩)(ρ) − (id ⊗ ℳ)(ρ)‖₁`. -/
noncomputable def diamondNorm {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (N M : QChannel a b) : ℝ :=
  sSup {x : ℝ | ∃ (n : ℕ) (ρ : Matrix (Fin n × a) (Fin n × a) ℂ), IsDensityOperator ρ ∧
    x = traceDist (N.tensorIdApply (Fin n) ρ) (M.tensorIdApply (Fin n) ρ)}

end WildeQIT


