-- Prove2me | Definitions.Def_QuadStatRE_Main_LeakageFamily
-- name    : QuadStatRE_Main_LeakageFamily
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T22:46:01.567649+00:00
-- url     : https://prove2.me/theorems/0f10b425-8281-4427-ad7b-43ed8684598a
-- title:
--   Leakage families, the mixture $M$, the equality leakage $W_0$ and affine symmetry (§3.2, §6.1)
-- statement:
--   With $G=\mathbb F_2^3$, a **leakage family** $W=(W_s)_{s\in G}$ on a finite transcript alphabet $\Omega$ is a collection of distributions on $\Omega$, one for each secret $s$ (p. 18, p. 28). Its **mixture** is $M=\frac18\sum_{s\in G}W_s$.
--
--   The **equality leakage** $W_{0,s}$ (p. 17) chooses $V\in\mathbb F_2^3$ uniformly and reveals $(V,e)$ with $e=\mathbf 1[V=s]$; as a distribution on $G\times\mathbb F_2$,
--   $$W_{0,s}(V,e)=\begin{cases}1/8,& e=\mathbf 1[V=s],\\ 0,&\text{otherwise.}\end{cases}$$
--
--   $W$ is **affine-symmetric** (p. 18) if for every invertible $P\in\mathbb F_2^{3\times3}$ and every $h\in\mathbb F_2^3$ the affine map $\varphi(s)=Ps+h$ is implemented by one permutation $\pi_\varphi$ of $\Omega$: whenever $T\leftarrow W_s$, $\pi_\varphi(T)$ has distribution $W_{\varphi(s)}$, i.e. $W_{\varphi(s)}(\pi_\varphi(\omega))=W_s(\omega)$ for all $s$ and $\omega$.
--
--   These are the objects of the privacy analysis: leakage families are channels from secrets to transcripts, and affine symmetry is what makes the $\chi^2$ Gram matrix take only two values.
--
--   **Formalization Note.** Distributions are functions $\Omega\to\mathbb R$; `IsLeakageFamily W` says each $W_s$ is nonnegative with total mass one. The permutation depends only on $(P,h)$, never on $s$.
-- source:
--   Applebaum, Quadratic Statistical Randomized Encoding for All Functions, STOC 2027 submission (manuscript sha256 000cbf4e…), pp. 17–18, §3.2; p. 28, §6.1

import Mathlib
import Definitions.Def_QuadraticRE_SD
import Definitions.Def_QuadStatRE_Main_BasicEncoding

namespace QuadStatRE.Main

open QuadraticRE

/-- A leakage family (Applebaum, *Quadratic Statistical Randomized Encoding for All Functions*,
STOC 2027 submission, p. 18 and §6.1, p. 28): `W = (W_s)_{s ∈ G}` on a finite transcript alphabet `Ω`,
"a collection of distributions on `Ω`, one for each value `s` of the secret". Distributions are
functions `Ω → ℝ`; this predicate says each `W s` is one. -/
def IsLeakageFamily {Ω : Type} [Fintype Ω] (W : G → Ω → ℝ) : Prop :=
  ∀ s, IsLaw (W s)

/-- The uniform mixture `M = (1/8) ∑_{s ∈ G} W_s` (§5.2, p. 25; §6.1, p. 28). -/
noncomputable def mix {Ω : Type} (W : G → Ω → ℝ) : Ω → ℝ :=
  fun ω => (1 / 8 : ℝ) * ∑ s : G, W s ω

/-- The equality leakage `W_{0,s}` (§3.2, p. 17): "choosing `V ∈ F₂³` uniformly at random and
revealing `(V, e)`, `e := 1[V = s]`". On the alphabet `G × F₂` it gives `(V, e)` probability `1/8`
when `e = 1[V = s]` and `0` otherwise. -/
noncomputable def W0 (s : G) : G × F2 → ℝ :=
  fun p => if p.2 = (if p.1 = s then 1 else 0) then (1 / 8 : ℝ) else 0

/-- Affine symmetry (p. 18): "for every invertible matrix `P ∈ F₂^{3×3}` and every vector `h ∈ F₂³`,
the affine map `φ(s) = Ps + h` can be implemented by a permutation `π_φ` of `Ω`: whenever `T ← W_s`,
the relabeled leakage transcript `π_φ(T)` has distribution `W_{φ(s)}`". One permutation serves all
secrets `s`; `π(T) ∼ W_{φ(s)}` for `T ∼ W_s` is `W_{φ(s)}(π ω) = W_s(ω)` for every `ω`. -/
def AffineSymmetric {Ω : Type} (W : G → Ω → ℝ) : Prop :=
  ∀ P : Matrix (Fin 3) (Fin 3) F2, IsUnit P → ∀ h : G,
    ∃ π : Equiv.Perm Ω, ∀ (s : G) (ω : Ω), W (P.mulVec s + h) (π ω) = W s ω

end QuadStatRE.Main


