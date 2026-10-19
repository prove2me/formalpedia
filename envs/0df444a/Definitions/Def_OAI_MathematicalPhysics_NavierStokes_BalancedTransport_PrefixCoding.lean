-- Prove2me | Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_PrefixCoding
-- name    : OAI_MathematicalPhysics_NavierStokes_BalancedTransport_PrefixCoding
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T02:39:34.338983+00:00
-- url     : https://prove2.me/theorems/fe9e0855-c545-4e14-ae77-7da7cdae0d75
-- title:
--   Base-$r$ coding of words and streams
-- statement:
--   This is part of the construction of smooth forced incompressible Navier–Stokes flows on $\mathbb R^3$ whose fluid particles simulate a Turing machine: a fixed particle enters a fixed box exactly when the machine halts. A field is a function $v(t,x)$ of time $t\in\mathbb R$ and position $x\in\mathbb R^3$, and a velocity is a field with values in $\mathbb R^3$.
--
--   Fix $r\in\mathbb R$ and a digit map $\delta$ from an alphabet $S$ to $\mathbb R$. This module codes words and streams as real numbers.
--
--   1. **Words.** The value of $w=a_1\cdots a_m$ is $\sum_{i=1}^mr^i\delta(a_i)$, defined recursively by $\mathrm{word}(a\,w)=r(\delta(a)+\mathrm{word}(w))$.
--   2. **Prefixed points.** $\mathrm{word}(w)+r^{m}z$, the point obtained by writing $w$ in front of the number $z$.
--   3. **Intervals.** $[\mathrm{word}(w),\mathrm{word}(w)+r^m]$, which contains every point with prefix $w$ when $z\in[0,1]$.
--   4. **Replacement.** The affine map $x\mapsto\mathrm{word}(v)+\frac{r^{|v|}}{r^{|u|}}(x-\mathrm{word}(u))$, which carries the interval of $u$ onto the interval of $v$, rewriting the prefix $u$ as $v$.
--   5. **Streams.** For a digit map into $\{0,\dots,B-1\}$, a stream $s$ is coded by the base-$B$ expansion $\sum_{n\ge0}\delta(s_n)B^{-(n+1)}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/PrefixCoding.lean

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/PrefixCoding.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BalancedThreeStack mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BalancedThreeStack
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FlatBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveArithmetic
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RationalAlgorithms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveExp
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RecorderRules

namespace OAI

noncomputable section
namespace BalancedTransport.Recorder
open Stream'
variable {Q Γ : Type*}

namespace Exec

variable {M : Machine Q Γ}

end Exec

variable (M : Machine Q Γ)
open Letter Control

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.Coding
variable {S : Type*}

def word (r : ℝ) (digit : S → ℝ) : List S → ℝ
  | [] => 0
  | a :: w => r * (digit a + word r digit w)

def prefixPoint (r : ℝ) (digit : S → ℝ) (w : List S) (z : ℝ) : ℝ :=
  word r digit w + r ^ w.length * z

def interval (r : ℝ) (digit : S → ℝ) (w : List S) : Set ℝ :=
  Set.Icc (word r digit w) (word r digit w + r ^ w.length)

@[simp] theorem word_nil (r : ℝ) (digit : S → ℝ) : word r digit [] = 0 := rfl

@[simp] theorem prefix_nil (r : ℝ) (digit : S → ℝ) (z : ℝ) :
    prefixPoint r digit [] z = z := by simp [prefixPoint]

@[simp] theorem prefix_cons (r : ℝ) (digit : S → ℝ) (a : S)
    (w : List S) (z : ℝ) :
    prefixPoint r digit (a :: w) z = r * (digit a + prefixPoint r digit w z) := by
  simp only [prefixPoint, word, List.length_cons, pow_succ]
  ring

def replacement (r : ℝ) (digit : S → ℝ) (u v : List S) (x : ℝ) : ℝ :=
  word r digit v + (r ^ v.length / r ^ u.length) * (x - word r digit u)

def stream {B : ℕ} (digit : S → Fin B) (s : Stream' S) : ℝ :=
  Real.ofDigits (fun n => digit (s n))

end BalancedTransport.Coding
end

noncomputable section
namespace BalancedTransport.Coding
variable {S : Type*}
open Stream'

end BalancedTransport.Coding
end

end OAI


