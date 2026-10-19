-- Prove2me | Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
-- name    : OAI_Analysis_Littlewood_BinaryPacket
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T03:57:58.241574+00:00
-- url     : https://prove2.me/theorems/236d55a0-bcc1-4dbf-abc6-f1cb3541c511
-- title:
--   Recursive binary trigonometric polynomials on tori, their energy, and primitive frequency vectors
-- statement:
--   Let $\mathbb{T}=\mathbb{R}/\mathbb{Z}$ carry its Haar probability measure and $\mathbb{T}^n$ the product measure. For $s\in\mathbb{Z}^n$ let $e_s(x)=\exp\bigl(2\pi i\sum_{k}s_k x_k\bigr)$ be the corresponding character of $\mathbb{T}^n$.
--
--   1. **Cosine.** $c(x)=\operatorname{Re}e^{2\pi i x}=\cos(2\pi x)$ for $x\in\mathbb{T}$; it is continuous.
--
--   2. **Binary functions.** Functions $B_n:\mathbb{T}^n\to\mathbb{R}$ are defined recursively by $B_0=0$ and, for $x=(x_0,x_1,\dots,x_n)\in\mathbb{T}^{n+1}$ with tail $x'=(x_1,\dots,x_n)$,
--   $$
--   B_{n+1}(x)=B_n(x')+\frac{1-B_n(x')^2}{2}\,\cos(2\pi x_0).
--   $$
--   Each $B_n$ is continuous.
--
--   3. **Energy.** $E_n=\int_{\mathbb{T}^n}B_n(x)^2\,dx$.
--
--   4. **Primitive frequency vectors.** A vector $s\in\mathbb{Z}^n$ is primitive if $s\ne0$ and its first nonzero coordinate, in the order $s_0,s_1,\dots$, equals $1$ or $-1$. Recursively: no vector of $\mathbb{Z}^0$ is primitive, and $s\in\mathbb{Z}^{n+1}$ is primitive if and only if $s_0=1$, or $s_0=-1$, or $s_0=0$ and $(s_1,\dots,s_n)$ is primitive.
--
--   5. **Positive frequency vectors.** Likewise, $s$ is positive if $s\ne0$ and its first nonzero coordinate equals $1$ (recursively: $s_0=1$, or $s_0=0$ and the tail is positive).
--
--   6. **Spectral span.** For a predicate $P$ on $\mathbb{Z}^n$, $\mathcal{S}(P)$ is the complex linear span of the characters $e_s$ with $P(s)$, inside the space of all functions $\mathbb{T}^n\to\mathbb{C}$.
--
--   The recursion keeps $|B_n|\le1$ and increases the energy, $E_{n+1}\ge E_n+(1-E_n)^2/8$, so that $E_n\to1$; at the same time $B_n$ lies in the span $\mathcal{S}(\text{primitive})$. Primitive vectors split into pairs $\{s,-s\}$ with exactly one positive member, and two positive vectors are real multiples of each other only if they are equal. Hence $B_n$ is a real trigonometric polynomial bounded by $1$, with mean square close to $1$, whose frequencies come in pairs $\pm s$ with pairwise nonparallel positive representatives. This is the starting datum of the Fourier-spreading step in the construction of flat Littlewood polynomials.
--
--   **Formalization Note** Local instances make the Haar probability measure `AddCircle.haarAddCircle` the volume measure on `UnitAddCircle`. `cosine x` is `(fourier 1 x).re`; `binary n` is defined by recursion on `n`, the new variable being `x 0` and the old ones `Fin.tail x`; `energy n` is a Bochner integral over `Fin n → UnitAddCircle`. `primitive` and `positive` are `Prop`-valued recursive predicates, and `spectrumSpan P` is the `Submodule ℂ` spanned by the functions `mFourier s` with `P s`. The members `cosine_continuous` and `binary_continuous` are the continuity lemmas.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/BinaryPacket.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/BinaryPacket.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the AsymptoticallyMinimalLittlewood mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uE uX

namespace AsymptoticallyMinimalLittlewood
namespace Auxiliary
noncomputable section
open MeasureTheory Filter Topology Complex
open scoped BigOperators ComplexConjugate ENNReal
local instance instMeasureSpaceUnitAddCircle_oAI : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance instIsAddHaarMeasureUnitAddCircleVolume_oAI : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance instIsProbabilityMeasureUnitAddCircleVolume_oAI : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def cosine (x : UnitAddCircle) : ℝ := (fourier 1 x).re

@[fun_prop] lemma cosine_continuous : Continuous cosine := Complex.continuous_re.comp (fourier 1).continuous

def binary : (n : ℕ) → (Fin n → UnitAddCircle) → ℝ
  | 0, _ => 0
  | n+1, x => binary n (Fin.tail x) + (1-binary n (Fin.tail x)^2)/2*cosine (x 0)

@[fun_prop] lemma binary_continuous (n : ℕ) : Continuous (binary n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
      have ht : Continuous (fun x : Fin (n+1) → UnitAddCircle ↦ Fin.tail x) := by fun_prop
      exact (ih.comp ht).add (((continuous_const.sub ((ih.comp ht).pow 2)).div_const 2).mul
        (cosine_continuous.comp (continuous_apply 0)))

def energy (n : ℕ) : ℝ := ∫ x : Fin n → UnitAddCircle, binary n x^2

open UnitAddTorus

def primitive : (n : ℕ) → (Fin n → ℤ) → Prop
  | 0, _ => False
  | n+1, s => s 0 = 1 ∨ s 0 = -1 ∨ (s 0 = 0 ∧ primitive n (Fin.tail s))

def spectrumSpan {n : ℕ} (P : (Fin n → ℤ) → Prop) :
    Submodule ℂ ((Fin n → UnitAddCircle) → ℂ) :=
  Submodule.span ℂ ((fun s ↦ (mFourier s : (Fin n → UnitAddCircle) → ℂ)) '' {s | P s})

def positive : (n : ℕ) → (Fin n → ℤ) → Prop
  | 0, _ => False
  | n+1, s => s 0=1 ∨ (s 0=0 ∧ positive n (Fin.tail s))

end
end Auxiliary
end AsymptoticallyMinimalLittlewood

end OAI


