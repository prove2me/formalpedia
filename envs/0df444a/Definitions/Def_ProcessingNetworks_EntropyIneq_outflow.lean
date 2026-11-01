-- Prove2me | Definitions.Def_ProcessingNetworks_EntropyIneq_outflow
-- name    : ProcessingNetworks_EntropyIneq_outflow
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:27:59.452998+00:00
-- url     : https://prove2.me/theorems/6d69718c-acb7-4f57-aeaa-c7758725d1b6
-- title:
--   (B.14), p.269 — outflow rate $P_{i0}=1-\sum_j P_{ij}$ to the outside world
-- statement:
--   Let $P$ be an $I\times I$ routing matrix and $\mathcal I=\{1,\dots,I\}$. For each class $i\in\mathcal I$,
--
--   $$
--   P_{i0}:=1-\sum_{j\in\mathcal I}P_{ij},
--   $$
--
--   the rate of routing from class $i$ to the external world, indexed by the extra class $0$. With $\mathcal I_+=\mathcal I\cup\{0\}$ one then has $\sum_{j\in\mathcal I_+}P_{ij}=1$ for every $i$ (B.15).
--
--   **Formalization Note** Classes are `Fin I` (numbered from $0$ in Lean). The book's class $0$ is not an element of `Fin I`; every sum over $\mathcal I_+$ in this mission is a sum over `Fin I` plus a separate term with $P_{i0}$.
-- source:
--   Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), Appendix B §B.4, eq. (B.14)–(B.15), p.269 (PDF 285)

import Mathlib

namespace ProcessingNetworks.EntropyIneq

/-- **Outflow probability `P_{i0}`** (Dai & Harrison, *Processing Networks*, pre-publication draft
2020-4-2, spnbook.org, Appendix B §B.4, eq. (B.14), p.269 (PDF 285)): for an `I × I` routing matrix
`P` and a class `i`, `P_{i0} := 1 − Σ_{j ∈ 𝓘} P_{ij}`, the rate at which class `i` routes to the
outside world ("class 0"). With it, `Σ_{j ∈ 𝓘₊} P_{ij} = 1` for each `i` (B.15), where
`𝓘₊ = 𝓘 ∪ {0}`.

**Formalization Note** Classes `𝓘 = {1, …, I}` are `Fin I` (0-based). The book's extra index `0`
of `𝓘₊` is not an element of `Fin I`: every sum over `j ∈ 𝓘₊` is written as a sum over `Fin I` plus
the separate term with `P_{i0} = outflow P i` (and the conventions `d₀ = α₀ = 1`). -/
def outflow {I : ℕ} (P : Matrix (Fin I) (Fin I) ℝ) (i : Fin I) : ℝ :=
  1 - ∑ j, P i j

end ProcessingNetworks.EntropyIneq


