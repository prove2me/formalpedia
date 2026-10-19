-- Prove2me | Definitions.Def_OAI_Analysis_Littlewood_SlotParameters
-- name    : OAI_Analysis_Littlewood_SlotParameters
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T04:16:25.026985+00:00
-- url     : https://prove2.me/theorems/e7a952cb-abb3-4fb2-a091-7781e20c1635
-- title:
--   Chunk counts and the explicit variance, vertex and bad-vertex parameters of the signed-slot packing
-- statement:
--   Fix natural numbers $r$ (number of slots), $L$ (period length), $R$ (periods per chunk) and $q$ (the modulus). Write $\bar r=r-1$ for the truncated natural difference ($\bar r=0$ if $r=0$); all other differences below are real.
--
--   1. **Chunk count.** For $B,q\in\mathbb{N}$, $\mathrm{cc}(B,q)=\lfloor(q-1)/B\rfloor$, computed with natural-number subtraction and division (so it is $0$ when $q=0$ or $B=0$).
--
--   With $\kappa_q=\mathrm{cc}(2RL,q)/q$:
--
--   2. **Variance parameter.**
--   $$
--   A_V(r,L,R,q)=3\Bigl(2\bigl(\bar r\,(1-2(R-2)L\kappa_q)+2\bar r^{2}(2RL+1)\tfrac1q\bigr)+\bar r^{2}\bigl(1-2(R-2)L\kappa_q+2(R-2)L\tfrac1q\bigr)\Bigr).
--   $$
--
--   3. **Vertex parameter.** $N_V(r,L,R,q)=r\,(R-1)\,\kappa_q$.
--
--   4. **Limits as $q\to\infty$.** $A_\infty(r,R)=\dfrac{6(2\bar r+\bar r^{2})}{R}$ and $N_\infty(r,L,R)=\dfrac{r(1-1/R)}{2L}$.
--
--   5. **Bad-vertex parameters.** For real $e,p$,
--   $$
--   B_V(r,L,R,e,p,q)=\frac{r\max\bigl(A_V(r,L,R,q),0\bigr)}{(ep/2)^2},\qquad B_\infty(r,R,e,p)=\frac{r\,A_\infty(r,R)}{(ep/2)^2}.
--   $$
--
--   These are the explicit parameters of the slot construction modulo a prime $q$ with $K=\mathrm{cc}(2RL,q)$ chunks and period length $L$. The averaged squared deviation of the slot densities from $p=(1/(2L))^{r-1}$ is at most $A_V$, the slot hypergraph has exactly $q\,N_V$ vertices, and $q\,B_V$ is the resulting Chebyshev bound for the number of vertices whose density deviates from $p$ by at least $ep/2$. Since $\mathrm{cc}(B,q)/q\to1/B$, for fixed $L,R\ge1$ one has $A_V\to A_\infty$, $N_V\to N_\infty$ and $B_V\to B_\infty$ as $q\to\infty$, while $A_\infty\to0$ and $N_\infty\to r/(2L)$ as $R\to\infty$. This allows the repetition number $R$ to be fixed first and the prime $q$ to be taken large afterwards.
--
--   **Formalization Note** `chunkCount B q` is the natural number `(q-1)/B`; `packingAV r L R q`, `packingNV r L R q`, `packingALimit r R`, `packingNLimit r L R`, `packingBV r L R e p q` and `packingBLimit r R e p` are real-valued, with $\bar r$ written `((r-1 : ℕ) : ℝ)` and $R-2$, $R-1$ computed in $\mathbb{R}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/SlotParameters.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/SlotParameters.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the AsymptoticallyMinimalLittlewood mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail
import Definitions.Def_OAI_Analysis_Littlewood_Spreading
import Definitions.Def_OAI_Analysis_Littlewood_ProductProbability
import Definitions.Def_OAI_Analysis_Littlewood_Nibble
import Definitions.Def_OAI_Analysis_Littlewood_Averages
import Definitions.Def_OAI_Analysis_Littlewood_FiniteRank
import Definitions.Def_OAI_Analysis_Littlewood_Chunks
import Definitions.Def_OAI_Analysis_Littlewood_DependentMoments
import Definitions.Def_OAI_Analysis_Littlewood_SlotGraph

namespace OAI

universe uV

/-! Parameter choices for the concrete signed-slot packing. The chunk
length is chosen first and remains fixed while the prime modulus grows. -/
namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open Filter Topology
open scoped BigOperators

def chunkCount (B q : ℕ) : ℕ := (q-1)/B

def packingAV (r L R q : ℕ) : ℝ :=
  let k := (chunkCount (2*R*L) q : ℝ)/(q : ℝ)
  let u := 1/(q : ℝ)
  3*(2*(((r-1 : ℕ) : ℝ)*(1-2*((R : ℝ)-2)*L*k)+
    2*((r-1 : ℕ) : ℝ)^2*(2*(R : ℝ)*L+1)*u)+
    ((r-1 : ℕ) : ℝ)^2*(1-2*((R : ℝ)-2)*L*k+2*((R : ℝ)-2)*L*u))

def packingNV (r L R q : ℕ) : ℝ :=
  (r : ℝ)*((R : ℝ)-1)*((chunkCount (2*R*L) q : ℝ)/(q : ℝ))

def packingALimit (r R : ℕ) : ℝ :=
  6*(2*((r-1 : ℕ) : ℝ)+((r-1 : ℕ) : ℝ)^2)/(R : ℝ)

def packingNLimit (r L R : ℕ) : ℝ :=
  (r : ℝ)*(1-1/(R : ℝ))/(2*(L : ℝ))

def packingBV (r L R : ℕ) (e p : ℝ) (q : ℕ) : ℝ :=
  (r : ℝ)*max (packingAV r L R q) 0/(e*p/2)^2

def packingBLimit (r R : ℕ) (e p : ℝ) : ℝ :=
  (r : ℝ)*packingALimit r R/(e*p/2)^2

end
end AsymptoticallyMinimalLittlewood.Packing

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset Nibble Filter Topology
attribute [local instance] Classical.propDecidable

end
end AsymptoticallyMinimalLittlewood.Packing

end OAI


