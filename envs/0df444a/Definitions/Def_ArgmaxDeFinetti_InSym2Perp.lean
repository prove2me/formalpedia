-- Prove2me | Definitions.Def_ArgmaxDeFinetti_InSym2Perp
-- name    : ArgmaxDeFinetti_InSym2Perp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:41:37.168192+00:00
-- url     : https://prove2.me/theorems/5d5d7854-a9f2-4e23-a94c-27647cde9bc7
-- title:
--   The subspace $\mathrm{Sym}^2(u^\perp)$
-- statement:
--   For a unit vector $u\in\mathbb C^d$, let $P_{u^\perp}=I-|u\rangle\langle u|$ be the orthogonal projector onto $u^\perp=\{v:\langle u,v\rangle=0\}$. A two-site vector $\zeta$ lies in $\mathrm{Sym}^2(u^\perp)$ when
--   $$
--   \zeta\in\mathrm{Sym}^2(\mathbb C^d)\quad\text{and}\quad (P_{u^\perp}\otimes P_{u^\perp})\,\zeta=\zeta .
--   $$
--   This is the component of $\eta_u$ controlled by the argmax estimate (3.8)–(3.9).
--
--   **Formalization Note** $\mathrm{Sym}^2(u^\perp)$ is realized inside $\mathbb C^d\otimes\mathbb C^d$ as $\mathrm{Sym}^2(\mathbb C^d)\cap(u^\perp\otimes u^\perp)$; the definition is used for unit $u$.
-- source:
--   Jeronimo, Wu, Xu, Optimal Quantum de Finetti Theorems via Argmax Rounding, arXiv:2608.02590 (held version, sha256 fb339472…), §2, p.18 (u⊥) and §3.1.2, p.23, eq. (3.8)

import Mathlib
import Definitions.Def_ArgmaxDeFinetti_IsSym

open Matrix

namespace ArgmaxDeFinetti

/-- `P_{u⊥} = I − |u⟩⟨u|`, the orthogonal projector onto `u⊥ = {v : ⟨u, v⟩ = 0}` for a unit vector `u`,
Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), §2, p.18 (definition of `u⊥`). -/
def perpProj {d : ℕ} (u : Fin d → ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  1 - Matrix.vecMulVec u (star u)

/-- `P_{u⊥} ⊗ P_{u⊥}` on two sites, Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), §3.1, pp.23, 26. -/
def perp2 {d : ℕ} (u : Fin d → ℂ) : Op 2 d :=
  fun a b => perpProj u (a 0) (b 0) * perpProj u (a 1) (b 1)

/-- `ζ ∈ Sym²(u⊥)`: `ζ` is a symmetric two-site vector lying in `u⊥ ⊗ u⊥`, Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), eq. (3.8), p.23.

**Formalization Note** Used for unit `u`, where `perp2 u` is the projector onto `u⊥ ⊗ u⊥`; `Sym²(u⊥)` is the
intersection `Sym²(H) ∩ (u⊥ ⊗ u⊥)`. -/
def InSym2Perp {d : ℕ} (u : Fin d → ℂ) (ζ : Vec 2 d) : Prop :=
  IsSym ζ ∧ perp2 u *ᵥ ζ = ζ

end ArgmaxDeFinetti


