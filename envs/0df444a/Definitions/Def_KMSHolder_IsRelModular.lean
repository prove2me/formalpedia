-- Prove2me | Definitions.Def_KMSHolder_IsRelModular
-- name    : KMSHolder_IsRelModular
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:40:49.164847+00:00
-- url     : https://prove2.me/theorems/c4fafb3e-9c85-476b-868b-8dbd95c3808e
-- title:
--   Relative modular operator $\Delta_{\phi,\Omega}$
-- statement:
--   Let $M$ act on $H$ with cyclic and separating unit vector $\Omega$, and let $\phi$ be a positive normal functional on $M$. The paper defines $S_{\phi,\Omega} A\Omega = \xi_\phi(A^*)$ through the semi-cyclic representation of $\phi$, takes the polar decomposition $\overline{S_{\phi,\Omega}} = J_{\phi,\Omega}\Delta^{1/2}_{\phi,\Omega}$, and sets $\Delta_{\phi,\Omega} = S^*_{\phi,\Omega}\overline{S_{\phi,\Omega}}$.
--
--   A positive self-adjoint operator $T$ **is the relative modular operator $\Delta_{\phi,\Omega}$** when:
--
--   1. for every $a \in M$, $a\Omega$ lies in the domain of $T^{1/2}$ and $\|T^{1/2} a\Omega\|^2 = \phi(a a^*)$;
--   2. $M\Omega$ is a core for $T^{1/2}$: every point $(x, T^{1/2}x)$ of the graph of $T^{1/2}$ is a limit of points $(a_k\Omega, T^{1/2}a_k\Omega)$ with $a_k \in M$.
--
--   Since $\|\xi_\phi(a^*)\|^2 = \phi(a a^*)$ and $\|\Delta^{1/2}_{\phi,\Omega}x\| = \|\overline{S_{\phi,\Omega}}x\|$ on the common domain, $\Delta_{\phi,\Omega}$ satisfies both conditions. A positive self-adjoint operator is determined by its closed form $x \mapsto \|T^{1/2}x\|^2$, which the two conditions fix as the closure of $a\Omega \mapsto \phi(aa^*)$, so $T$ is unique. For $\phi = \omega$ it is the modular operator $\Delta$.
--
--   **Formalization Note** $T^{1/2}$ is taken with the support convention (`posPowGraph`), so $\ker T \ne 0$ (non-faithful $\phi$) is allowed. The positive normal functional is a function on all operators of which only the values on $M$ matter.
-- source:
--   Jäkel–Robl, The Hölder Inequality for KMS States, arXiv:1103.3608v2, §3.1, p.4

import Mathlib
import Definitions.Def_BoundedRecovery
import Definitions.Def_KMSHolder_PosSpectralCalculus
import Definitions.Def_KMSHolder_posPowGraph

open OAI.BoundedRecovery
open Filter Topology

namespace KMSHolder

/-- Jäkel–Robl, arXiv:1103.3608v2, §3.1, p.4: `T` is the relative modular operator `Δ_{φ,Ω}` of
a positive normal functional `φ` on `M` with respect to the cyclic separating vector `Ω` of
standard modular data `S`. The paper defines `S_{φ,Ω} AΩ = ξ_φ(A*)` (semi-cyclic
representation), `\overline{S_{φ,Ω}} = J_{φ,Ω} Δ^{1/2}_{φ,Ω}` and `Δ_{φ,Ω} = S*_{φ,Ω}\overline{S_{φ,Ω}}`.
Here `T` is characterized by its square root:
1. for every `a ∈ M`, `aΩ` is in the domain of `T^{1/2}` and `‖T^{1/2} aΩ‖² = φ(a a*)`
   (`= ‖ξ_φ(a*)‖² = ‖S_{φ,Ω} aΩ‖²`);
2. `MΩ` is a core for `T^{1/2}`: every point `(x, v)` of the graph of `T^{1/2}` is a limit of
   points `(aₖΩ, T^{1/2}aₖΩ)` with `aₖ ∈ M`.

**Formalization Note.** Since `Δ_{φ,Ω} = S*S̄`, `‖Δ^{1/2}_{φ,Ω} x‖ = ‖S̄ x‖` with the same domain,
and `MΩ` is a core of `S̄`; a positive self-adjoint operator is determined by its closed form
`x ↦ ‖T^{1/2}x‖²`, which conditions 1–2 fix as the closure of `aΩ ↦ φ(aa*)`. So `T` is unique,
and for `φ = ω` it is the modular operator. The kernel of `T` is allowed (non-faithful `φ`);
`T^{1/2}` follows the support convention of `posPowGraph`. -/
def IsRelModular {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : StandardModularData H) (φ : (H →L[ℂ] H) → ℂ) (T : PosSpectralCalculus H) : Prop :=
  (∀ a ∈ S.M, ∃ v : H, (a S.xi, v) ∈ posPowGraph T (1 / 2) ∧
      ‖v‖ ^ 2 = (φ (a * star a)).re) ∧
    ∀ x v : H, (x, v) ∈ posPowGraph T (1 / 2) →
      ∃ (a : ℕ → H →L[ℂ] H) (w : ℕ → H),
        (∀ k, a k ∈ S.M ∧ (a k S.xi, w k) ∈ posPowGraph T (1 / 2)) ∧
        Tendsto (fun k => a k S.xi) atTop (𝓝 x) ∧ Tendsto w atTop (𝓝 v)

end KMSHolder


