-- Prove2me | Definitions.Def_StableMSR_LogicalAssemblyColumns
-- name    : StableMSR_LogicalAssemblyColumns
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-23T22:25:12.625799+00:00
-- url     : https://prove2.me/theorems/92fdcadc-ab26-4ebf-b1fa-26012a6cb59c
-- title:
--   Six logical gate columns of the ordered regional assembly
-- statement:
--   The staging representation records the original row count, gate count, tags, two predecessor fields, regional roots, and gate-major point memberships on six interleaved integer tapes. Its native generator is required to compute these values within the stability bound. Header addresses, column strides, arena capacity, and the final ready state are supplied by the formatter.
-- source:
--   Implementation interface for the dense singleton circuits in Ravichandran and Reyzin, Appendix A.6, pp. 21–22, https://arxiv.org/abs/2611.03547.

import Definitions.Def_StableMSR_DenseGlobalAssembly
namespace StableMSR.Recovery.NativeWriter
open Compiler OracleQueries SingleCircuit SingleRAM WindowCSP
set_option autoImplicit false

/-- Address of word i in logical gate column j. -/
def word (j i : ℕ) : ℤ := -(32 + 8*(i:ℤ) + (j:ℤ))

/-- Gate data in gate-major order. Only actual tag, edge, root and bitmap words are prescribed. -/
def Columns (n k S : ℕ) (g : Gates) (roots : ℕ → ℕ) (s : Store) : Prop :=
  s.ptrs 0=(n:ℤ) ∧ s.ptrs 1=(k:ℤ) ∧ s.imem (word 0 0)=(g.size:ℤ) ∧ s.imem (word 0 1)=(S:ℤ) ∧
  (∀ p<g.size, s.imem (word 1 p)=opCode (gateAt g p) ∧
    s.imem (word 2 p)=(leftID (gateAt g p):ℤ) ∧ s.imem (word 3 p)=(rightID (gateAt g p):ℤ)) ∧
  (∀ r<3*g.size, s.imem (word 4 r)=(roots r:ℤ)) ∧
  ∀ p<g.size, ∀ i<n, s.imem (word 5 (p*n+i))=
    (if (tinyMask (gateAt g p)).contains i then 1 else 0)

/-- Uniform computation of the six logical columns of the specified regional assembly. -/
def GeneratesColumns (e : ℚ) (c D b : ℕ) (cmd : Cmd) : Prop :=
  ∀ (x : World) (s : Store), 1 ≤ x.k → x.k < x.n → IsMetricArray x.dist → Ready x s →
    let a := globalAssembly x (budget (e:ℝ)) (widthBound (e:ℝ))
    ∃ t z, Executes x.dist cmd s t z ∧ z ≤ c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
      Columns x.n x.k x.rows a.gates a.roots t

end StableMSR.Recovery.NativeWriter


