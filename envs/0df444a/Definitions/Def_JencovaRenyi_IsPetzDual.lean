-- Prove2me | Definitions.Def_JencovaRenyi_IsPetzDual
-- name    : JencovaRenyi_IsPetzDual
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:41:52.059447+00:00
-- url     : https://prove2.me/theorems/13f62f19-df79-4717-b3a8-8dce993af8a9
-- title:
--   The pairs $(x, x')$ with $\Phi(h_x) = \Phi(h_\varphi)_{x'}$ and the Petz dual $\Phi_\varphi(h_0)$
-- statement:
--   Let $\Phi : L_1(\mathcal M)\to L_1(\mathcal N)$ be positive linear trace preserving and $\varphi$ a normal state; write $h'_y$ for the symmetric embedding of $y\in\mathcal N$ with respect to $\Phi(\varphi)$.
--
--   1. $(x, y)\in\mathcal M\times\mathcal N$ is a **Petz pair** if $\Phi(h_x) = h'_y = \Phi(h_\varphi)^{1/2}\,y\,\Phi(h_\varphi)^{1/2}$. The paper's $x' = \Phi^*_\varphi(x)$ is the unique such $y$ in $e'\mathcal Ne'$, $e' = s(\Phi(\varphi))$.
--   2. $g\in L_1(\mathcal M)$ is the **Petz dual** $g = \Phi_\varphi(h_0)$ of $h_0 \in L_1(\mathcal N)$, the preadjoint of $\Phi^*_\varphi$, if $g = ege$ and
--   $$
--   g(x) = \operatorname{Tr}\Phi_\varphi(h_0)\,x = \operatorname{Tr} h_0\,\Phi^*_\varphi(x) = h_0(y)
--   $$
--   for every Petz pair $(x, y)$, as in (16).
--
--   The Petz dual is the adjoint of $\Phi$ for the $L_p$–$L_q$ duality and enters the bounds of Theorem 3.14.
--
--   **Formalization Note** Stated without support projections. For $h_0 = e'h_0e'$, $h_0(y)$ depends only on $e'ye' = \Phi^*_\varphi(exe)$, and every $x$ has a Petz partner (milestone `JencovaRenyi.petz_endpoints`), so $g$ is determined.
-- source:
--   Jenčová, Rényi relative entropies and noncommutative $L_p$-spaces, arXiv:1609.08462v4, §3.3, p.16 (the map $x\mapsto x'$, $\Phi^*_\varphi$, and (16))

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P06
import Definitions.Def_JencovaRenyi_Predual
import Definitions.Def_JencovaRenyi_symmEmbed

open QAlgorithms.Papers.Independent.Claimed50.P06

namespace JencovaRenyi

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- `y = x'` (Jenčová, arXiv:1609.08462v4, §3.3, p.16): `Φ(h_x) = Φ(h_φ)_{y}`, i.e. the image
of `h_x = h_φ^{1/2} x h_φ^{1/2}` under `Φ` is the symmetric embedding of `y ∈ N` for the
state `Φ(φ)`. The paper's `Φ*_φ(exe) = x'` is the unique such `y` in `e'Ne'`,
`e' = s(Φ(φ))`. -/
def IsPetzPair {A : StarSubalgebra ℂ (H →L[ℂ] H)} {B : StarSubalgebra ℂ (K →L[ℂ] K)}
    (SA : StandardForm A) (SB : StandardForm B) (Φ : Predual A →ₗ[ℂ] Predual B)
    (φ : Predual A) (x : A) (y : B) : Prop :=
  Φ (symmEmbed SA φ x) = symmEmbed SB (Φ φ) y

/-- `g = Φ_φ(h₀)`, the Petz dual (Jenčová, arXiv:1609.08462v4, §3.3, (16), p.16): the preadjoint of
`Φ*_φ : eMe → e'Ne'`. That is, `g = ege` (`e = s(φ)`) and
`Tr Φ_φ(h₀) x = Tr h₀ Φ*_φ(x)`, stated as `g(x) = h₀(y)` for every `x ∈ M` and every `y ∈ N`
with `Φ(h_x) = Φ(h_φ)_y`.

**Formalization Note.** For `h₀ = e'h₀e'`, `h₀(y)` depends only on `e'ye' = Φ*_φ(exe)`, and
every `x` has such a `y` (milestone `petz_endpoints`), so `g` is determined. -/
def IsPetzDual {A : StarSubalgebra ℂ (H →L[ℂ] H)} {B : StarSubalgebra ℂ (K →L[ℂ] K)}
    (SA : StandardForm A) (SB : StandardForm B) (Φ : Predual A →ₗ[ℂ] Predual B)
    (φ : Predual A) (h₀ : Predual B) (g : Predual A) : Prop :=
  IsSupported φ g ∧
    ∀ (x : A) (y : B), IsPetzPair SA SB Φ φ x y →
      (g : A →L[ℂ] ℂ) x = (h₀ : B →L[ℂ] ℂ) y

end JencovaRenyi


