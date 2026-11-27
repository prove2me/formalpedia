-- Prove2me | Definitions.Def_WildeQIT_Compression_Supplement_IsHadamard
-- name    : WildeQIT_Compression_Supplement_IsHadamard
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T04:00:48.076466+00:00
-- url     : https://prove2.me/theorems/f09278fd-bc0b-4bfb-995e-5b676b4669eb
-- title:
--   Quantum Hadamard channel (complement entanglement-breaking)
-- statement:
--   A quantum channel $\mathcal N_{A'\to B}$ is a **quantum Hadamard channel** if its complementary channel $\mathcal N^c_{A'\to E}$ is entanglement-breaking: for every reference system $R$ of finite dimension and every state $\rho_{RA'}$, the state $(\mathrm{id}_R\otimes\mathcal N^c)(\rho_{RA'})$ is separable.
--
--   Here $\mathcal N^c(\rho)=\operatorname{Tr}_B\{U^{\mathcal N}\rho\,U^{\mathcal N\dagger}\}$ for an isometric extension $U^{\mathcal N}_{A'\to BE}$ of $\mathcal N$. Generalized dephasing channels are Hadamard channels.
--
--   Hadamard channels have additive Holevo information (Theorem 20.4.1) and a single-letter quantum dynamic capacity region (Theorem 25.5.1).
--
--   **Formalization Note** The complementary channel is the published `WildeQIT.Degradable.complementaryApply` for the canonical isometric extension (environment indexed by the Kraus labels), packaged as a linear map; entanglement-breaking is the published `WildeQIT.EntBreaking.IsEntanglementBreaking`. Two complementary channels differ by an isometry or partial isometry on the environment, which preserves separability, so the property does not depend on the extension.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §5.2.3, p. 196; Definition 4.6.8, p. 166

import Mathlib
import Definitions.Def_WildeQIT_Degradable_complementaryApply
import Definitions.Def_WildeQIT_EntBreaking_IsEntanglementBreaking

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §5.2.3, p. 196
(quantum Hadamard channels), used in Theorem 20.4.1, p. 573, and §25.5.1, p. 713.
-/

open Matrix

namespace WildeQIT.Compression.Supplement

/-- **Quantum Hadamard channel** (Wilde, *From Classical to Quantum Shannon Theory*,
arXiv:1106.1445v8, §5.2.3, p. 196): a quantum channel whose complementary channel is
entanglement-breaking (Definition 4.6.8).

**Formalization Note.** The complementary channel is the published
`WildeQIT.Degradable.complementaryApply N`, `ρ ↦ Tr_B{U^N ρ U^N†}` for the canonical isometric
extension `U^N` (environment = the Kraus index type `N.ι`), packaged as the linear map it is;
entanglement-breaking is the published `WildeQIT.EntBreaking.IsEntanglementBreaking`
(separable output for every finite reference and every input density operator). Any two
complementary channels of `N` differ by an isometry or partial isometry on the environment,
which maps separable states to separable states, so the property does not depend on the choice of
isometric extension. -/
def IsHadamard {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] (N : QChannel a b) : Prop :=
  WildeQIT.EntBreaking.IsEntanglementBreaking
    ({ toFun := WildeQIT.Degradable.complementaryApply N
       map_add' := by
         intro x y
         ext i j
         simp [WildeQIT.Degradable.complementaryApply, WildeQIT.partialTraceLeft,
           Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
       map_smul' := by
         intro c x
         ext i j
         simp [WildeQIT.Degradable.complementaryApply, WildeQIT.partialTraceLeft,
           Matrix.mul_smul, Matrix.smul_mul, Finset.mul_sum] } :
      Matrix a a ℂ →ₗ[ℂ] Matrix N.ι N.ι ℂ)

end WildeQIT.Compression.Supplement


