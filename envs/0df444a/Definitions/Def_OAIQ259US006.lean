-- Prove2me | Definitions.Def_OAIQ259US006
-- name    : OAIQ259US006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T18:10:00.093431+00:00
-- url     : https://prove2.me/theorems/b302161a-19ef-4ed9-9580-400a675c503e
-- title:
--   Definitions bundle OAIQ259US006 of the split of OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 264 declarations of OpenAI's Lean: 146 definitions, 1 inductive type or structure, 4 instances and 113 theorems. The definitions and types are `OAI.Saxl.Balance.Packing.join`, `OAI.Saxl.Balance.Packing.lift`, `OAI.Saxl.Balance.Packing.map`, `OAI.Saxl.Balance.Piece.lift`, `OAI.Saxl.Balance.WordPacking`, `OAI.Saxl.Balance.WordPacking.binaryBounded`, `OAI.Saxl.Balance.WordPacking.bounded`, `OAI.Saxl.Balance.WordPacking.cone`, `OAI.Saxl.Balance.WordPacking.empty`, `OAI.Saxl.Balance.WordPacking.join`, `OAI.Saxl.Balance.WordPacking.permute`, `OAI.Saxl.Balance.WordPacking.sorted`, `OAI.Saxl.Balance.appendShortTableau`, `OAI.Saxl.Balance.balanceColumns`, `OAI.Saxl.Balance.boundedPacking`, `OAI.Saxl.Balance.columnOutputSums`, `OAI.Saxl.Balance.columnRowSums`, `OAI.Saxl.Balance.constantOutputMap`, `OAI.Saxl.Balance.inOutputs`, `OAI.Saxl.Balance.neighborLayer`, `OAI.Saxl.Balance.neighborRight`, `OAI.Saxl.Balance.neighborTableau`, `OAI.Saxl.Balance.numericBands`, `OAI.Saxl.Balance.placedPiece`, `OAI.Saxl.Balance.projectedPiece`, `OAI.Saxl.Balance.runBands`, `OAI.Saxl.Balance.singleFiberHom`, `OAI.Saxl.Balance.twoPathLeft`, `OAI.Saxl.Balance.twoPathRight`, `OAI.Saxl.Columns.CompactDomains.atValue`, `OAI.Saxl.Columns.Domains.atValue`, `OAI.Saxl.Columns.Domains.weight`, `OAI.Saxl.Columns.Edge`, `OAI.Saxl.Columns.Perms`, `OAI.Saxl.Columns.certificateEdges`, `OAI.Saxl.Columns.chain`, `OAI.Saxl.Columns.columnEquiv`, `OAI.Saxl.Columns.columnPerm`, `OAI.Saxl.Columns.columnWedge`, `OAI.Saxl.Columns.compactEdgeOptions` and 107 more.
--
--   **Sources.** They come from these modules of lean/OAI/RepresentationTheory, in whole or in part: `Saxl_BandFactorization`, `Saxl_BandGlue`, `Saxl_BandOrbit`, `Saxl_BandPairing`, `Saxl_BandSupport`, `Saxl_ColumnContraction`, `Saxl_CoordinateSector`, `Saxl_CyclicSector`, `Saxl_CyclicTensor`, `Saxl_DominatedQuotient`, `Saxl_DominatedSupport`, `Saxl_HighProjection`, `Saxl_Model`, `Saxl_PathAlternation`, `Saxl_Polytabloid`, `Saxl_PositionSplit`, `Saxl_RepeatedProjection`, `Saxl_ShapeRigidity`, `Saxl_SignEquivalence`, `Saxl_SpechtClassification`, `Saxl_SpechtDuality`, `Saxl_SpechtSubmodule`, `Saxl_StaircaseSign`, `Saxl_SupportSeparation`, `UniversalSquare_Balance_BalanceAssembly`, `UniversalSquare_Balance_BalanceColumns`, `UniversalSquare_Balance_BalanceGluing`, `UniversalSquare_Balance_BalanceLeaves`, `UniversalSquare_Balance_BalanceLift`, `UniversalSquare_Balance_BalancePacking`, `UniversalSquare_Balance_ConstantOutputs`, `UniversalSquare_Balance_EmptyPacking`, `UniversalSquare_Balance_PackingSupport`, `UniversalSquare_Balance_WordPacking`, `UniversalSquare_Balance_WordPackingCone`, `UniversalSquare_Balance_WordPackingLeaves`, `UniversalSquare_Balance_WordPackingPairs`, `UniversalSquare_Band_OddPath`, `UniversalSquare_Band_OneExtra`, `UniversalSquare_Band_RunBands`, `UniversalSquare_Band_TwoPathGeometry`, `UniversalSquare_Capacity_NumericBands`, `UniversalSquare_Contraction_ChoiceContractions`, `UniversalSquare_Contraction_ColumnCertificates`, `UniversalSquare_Contraction_CompactDomainsCore`, `UniversalSquare_Contraction_DomainContractions`, `UniversalSquare_Contraction_DomainSolver`, `UniversalSquare_Contraction_PairForms`, `UniversalSquare_Contraction_PolynomialDetection`, `UniversalSquare_Contraction_SingletonForms`, `UniversalSquare_Contraction_SymmetricPairs`, `UniversalSquare_Finite_DegreePlans14`, `UniversalSquare_Finite_DegreeRegionData39`, `UniversalSquare_Semigroup_SemigroupTensor`, `UniversalSquare_Specht_AlternateColumns`, `UniversalSquare_Specht_ColumnReorder`, `UniversalSquare_Specht_ColumnRestriction`, `UniversalSquare_Specht_CountedPieri`, `UniversalSquare_Specht_FinitePieri`, `UniversalSquare_Specht_FlagColumns`, `UniversalSquare_Specht_NoMixedColumns`, `UniversalSquare_Specht_RepeatedColumns`, `UniversalSquare_Specht_ShortColumns`, `UniversalSquare_Specht_StandardColumns`, `UniversalSquare_Specht_ThreeRowColumns`, `UniversalSquare_Specht_ThreeRowGenerator`, `UniversalSquare_Specht_ThreeRowPieri`, `UniversalSquare_Specht_ThreeRowTensors`, `UniversalSquare_Specht_YoungConverse`, `UniversalSquare_Specht_ZeroColumns`, `UniversalSquare_Support_AttachmentTransfer`, `UniversalSquare_Support_CoordinateLine`, `UniversalSquare_Support_CountedGluing`, `UniversalSquare_Support_DualTransfer`, `UniversalSquare_Support_Neighboring`, `UniversalSquare_Support_ProjectedTensor`, `UniversalSquare_Support_WordContents`, `UniversalSquare_Support_WordRelabel`.
--
--   **Imports.** It imports the published bundle `Def_UniversalTensorSquares`; the bundles `OAIQ259US000` and `OAIQ259US001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ259US021` and `OAIQ259US022`; the statements `OAI.Saxl.Balance.PackingPlan.realize`, `OAI.Saxl.Balance.WordPacking.kronecker_pos`, `OAI.Saxl.Balance.WordPacking.neighbor`, `OAI.Saxl.Balance.WordPacking.threeRows`, `OAI.Saxl.Balance.balancePacking`, `OAI.Saxl.Balance.short_pair_support`, `OAI.Saxl.ThreeRow.generator_support`, `OAI.Saxl.ThreeRow.sixSquare_columns`, `OAI.Saxl.cyclic_saxl_conjecture`, `OAI.UniversalTensorSquare.rowSquare_choices`, `OAI.UniversalTensorSquare.rowSquare_compact`, `OAI.UniversalTensorSquare.smallCert13_24`, `OAI.UniversalTensorSquare.smallCert13_30`, `OAI.UniversalTensorSquare.smallCert13_4`, `OAI.UniversalTensorSquare.smallCert13_5`, `OAI.UniversalTensorSquare.smallCert13_6` and `OAI.UniversalTensorSquare.smallCert13_7`; the proofs of `OAI.Saxl.Balance.WordPacking.kronecker_pos`, `OAI.Saxl.Columns.two_path_cyclic_support_placed`, `OAI.Saxl.ThreeRow.sixSquare_columns`, `OAI.Saxl.saxl_kronecker_pos`, `OAI.UniversalTensorSquare.degreeTree39_117All`, `OAI.UniversalTensorSquare.degreeTree39_11All`, `OAI.UniversalTensorSquare.degreeTree39_17All`, `OAI.UniversalTensorSquare.degreeTree39_30All`, `OAI.UniversalTensorSquare.degreeTree41_5All`, `OAI.UniversalTensorSquare.degreeTree41_8All`, `OAI.UniversalTensorSquare.degreeTree43_107All`, `OAI.UniversalTensorSquare.degreeTree43_120All`, `OAI.UniversalTensorSquare.degreeTree43_123All`, `OAI.UniversalTensorSquare.degreeTree43_126All`, `OAI.UniversalTensorSquare.degreeTree43_128All`, `OAI.UniversalTensorSquare.degreeTree43_140All`, `OAI.UniversalTensorSquare.degreeTree43_182All`, `OAI.UniversalTensorSquare.degreeTree43_183All`, `OAI.UniversalTensorSquare.degreeTree43_197All`, `OAI.UniversalTensorSquare.degreeTree43_201All`, `OAI.UniversalTensorSquare.degreeTree43_211All`, `OAI.UniversalTensorSquare.degreeTree43_221All`, `OAI.UniversalTensorSquare.degreeTree43_238All`, `OAI.UniversalTensorSquare.degreeTree43_257All`, `OAI.UniversalTensorSquare.degreeTree43_264All`, `OAI.UniversalTensorSquare.degreeTree43_280All`, `OAI.UniversalTensorSquare.degreeTree43_296All`, `OAI.UniversalTensorSquare.degreeTree43_298All`, `OAI.UniversalTensorSquare.degreeTree43_321All`, `OAI.UniversalTensorSquare.degreeTree43_382All`, `OAI.UniversalTensorSquare.degreeTree43_43All`, `OAI.UniversalTensorSquare.degreeTree43_493All`, `OAI.UniversalTensorSquare.degreeTree43_540All`, `OAI.UniversalTensorSquare.degreeTree43_56All`, `OAI.UniversalTensorSquare.degreeTree43_583All`, `OAI.UniversalTensorSquare.degreeTree43_585All`, `OAI.UniversalTensorSquare.degreeTree43_59All`, `OAI.UniversalTensorSquare.degreeTree43_645All`, `OAI.UniversalTensorSquare.degreeTree43_68All`, `OAI.UniversalTensorSquare.degreeTree43_77All`, `OAI.UniversalTensorSquare.degreeTree43_80All`, `OAI.UniversalTensorSquare.degreeTree43_82All`, `OAI.UniversalTensorSquare.degreeTree43_83All`, `OAI.UniversalTensorSquare.degreeTree43_85All`, `OAI.UniversalTensorSquare.degreeTree43_95All`, `OAI.UniversalTensorSquare.degreeTree43_97All`, `OAI.UniversalTensorSquare.degreeTree43_99All`, `OAI.UniversalTensorSquare.degreeTree62_1000All`, `OAI.UniversalTensorSquare.degreeTree62_1005All`, `OAI.UniversalTensorSquare.degreeTree62_1016All`, `OAI.UniversalTensorSquare.degreeTree62_107All`, `OAI.UniversalTensorSquare.degreeTree62_115All`, `OAI.UniversalTensorSquare.degreeTree62_140All`, `OAI.UniversalTensorSquare.degreeTree62_148All`, `OAI.UniversalTensorSquare.degreeTree62_166All`, `OAI.UniversalTensorSquare.degreeTree62_178All`, `OAI.UniversalTensorSquare.degreeTree62_195All`, `OAI.UniversalTensorSquare.degreeTree62_210All`, `OAI.UniversalTensorSquare.degreeTree62_212All`, `OAI.UniversalTensorSquare.degreeTree62_216All`, `OAI.UniversalTensorSquare.degreeTree62_220All`, `OAI.UniversalTensorSquare.degreeTree62_242All`, `OAI.UniversalTensorSquare.degreeTree62_275All`, `OAI.UniversalTensorSquare.degreeTree62_283All`, `OAI.UniversalTensorSquare.degreeTree62_298All`, `OAI.UniversalTensorSquare.degreeTree62_307All`, `OAI.UniversalTensorSquare.degreeTree62_317All`, `OAI.UniversalTensorSquare.degreeTree62_34All`, `OAI.UniversalTensorSquare.degreeTree62_38All`, `OAI.UniversalTensorSquare.degreeTree62_43All`, `OAI.UniversalTensorSquare.degreeTree62_44All`, `OAI.UniversalTensorSquare.degreeTree62_47All`, `OAI.UniversalTensorSquare.degreeTree62_505All`, `OAI.UniversalTensorSquare.degreeTree62_52All`, `OAI.UniversalTensorSquare.degreeTree62_576All`, `OAI.UniversalTensorSquare.degreeTree62_59All`, `OAI.UniversalTensorSquare.degreeTree62_5All`, `OAI.UniversalTensorSquare.degreeTree62_667All`, `OAI.UniversalTensorSquare.degreeTree62_715All`, `OAI.UniversalTensorSquare.degreeTree62_719All`, `OAI.UniversalTensorSquare.degreeTree62_736All`, `OAI.UniversalTensorSquare.degreeTree62_777All`, `OAI.UniversalTensorSquare.degreeTree62_857All`, `OAI.UniversalTensorSquare.degreeTree62_891All`, `OAI.UniversalTensorSquare.degreeTree62_94All`, `OAI.UniversalTensorSquare.degreeTree62_968All`, `OAI.UniversalTensorSquare.degreeTree62_985All`, `OAI.UniversalTensorSquare.degree_pos151`, `OAI.UniversalTensorSquare.degree_pos32`, `OAI.UniversalTensorSquare.degree_pos33`, `OAI.UniversalTensorSquare.degree_pos34`, `OAI.UniversalTensorSquare.degree_pos44`, `OAI.UniversalTensorSquare.degree_pos48`, `OAI.UniversalTensorSquare.degree_pos52`, `OAI.UniversalTensorSquare.degree_pos53`, `OAI.UniversalTensorSquare.degree_pos56`, `OAI.UniversalTensorSquare.degree_pos59`, `OAI.UniversalTensorSquare.degree_pos60`, `OAI.UniversalTensorSquare.degree_pos61`, `OAI.UniversalTensorSquare.sg10211`, `OAI.UniversalTensorSquare.sg10214`, `OAI.UniversalTensorSquare.sg10215`, `OAI.UniversalTensorSquare.sg10218`, `OAI.UniversalTensorSquare.sg10219`, `OAI.UniversalTensorSquare.sg10220`, `OAI.UniversalTensorSquare.sg10221`, `OAI.UniversalTensorSquare.sg10222`, `OAI.UniversalTensorSquare.sg10223`, `OAI.UniversalTensorSquare.sg10224`, `OAI.UniversalTensorSquare.sg10225`, `OAI.UniversalTensorSquare.sg10226`, `OAI.UniversalTensorSquare.sg10227`, `OAI.UniversalTensorSquare.sg10228`, `OAI.UniversalTensorSquare.sg10229`, `OAI.UniversalTensorSquare.sg10230`, `OAI.UniversalTensorSquare.sg10236`, `OAI.UniversalTensorSquare.sg10240`, `OAI.UniversalTensorSquare.sg10242`, `OAI.UniversalTensorSquare.sg10243`, `OAI.UniversalTensorSquare.sg10244`, `OAI.UniversalTensorSquare.sg10268`, `OAI.UniversalTensorSquare.sg10271`, `OAI.UniversalTensorSquare.sg10273`, `OAI.UniversalTensorSquare.sg10279`, `OAI.UniversalTensorSquare.sg10280`, `OAI.UniversalTensorSquare.sg10287`, `OAI.UniversalTensorSquare.sg10288`, `OAI.UniversalTensorSquare.sg10291`, `OAI.UniversalTensorSquare.sg10292`, `OAI.UniversalTensorSquare.sg10293`, `OAI.UniversalTensorSquare.sg10294`, `OAI.UniversalTensorSquare.sg10295`, `OAI.UniversalTensorSquare.sg10296`, `OAI.UniversalTensorSquare.sg10297`, `OAI.UniversalTensorSquare.sg10298`, `OAI.UniversalTensorSquare.sg10299`, `OAI.UniversalTensorSquare.sg10300`, `OAI.UniversalTensorSquare.sg10301`, `OAI.UniversalTensorSquare.sg10302`, `OAI.UniversalTensorSquare.sg10303`, `OAI.UniversalTensorSquare.sg10304`, `OAI.UniversalTensorSquare.sg10305`, `OAI.UniversalTensorSquare.sg10306`, `OAI.UniversalTensorSquare.sg10307`, `OAI.UniversalTensorSquare.sg10311`, `OAI.UniversalTensorSquare.sg10315`, `OAI.UniversalTensorSquare.sg10316`, `OAI.UniversalTensorSquare.sg10318`, `OAI.UniversalTensorSquare.sg10319`, `OAI.UniversalTensorSquare.sg10351`, `OAI.UniversalTensorSquare.sg10364`, `OAI.UniversalTensorSquare.sg10368`, `OAI.UniversalTensorSquare.sg10369`, `OAI.UniversalTensorSquare.sg10370`, `OAI.UniversalTensorSquare.sg10373`, `OAI.UniversalTensorSquare.sg10375`, `OAI.UniversalTensorSquare.sg10377`, `OAI.UniversalTensorSquare.sg10379`, `OAI.UniversalTensorSquare.sg10381`, `OAI.UniversalTensorSquare.sg10387`, `OAI.UniversalTensorSquare.sg10388`, `OAI.UniversalTensorSquare.sg10389`, `OAI.UniversalTensorSquare.sg10390`, `OAI.UniversalTensorSquare.sg10391`, `OAI.UniversalTensorSquare.sg10392`, `OAI.UniversalTensorSquare.sg10393`, `OAI.UniversalTensorSquare.sg10394`, `OAI.UniversalTensorSquare.sg10395`, `OAI.UniversalTensorSquare.sg10396`, `OAI.UniversalTensorSquare.sg10397`, `OAI.UniversalTensorSquare.sg10398`, `OAI.UniversalTensorSquare.sg10399`, `OAI.UniversalTensorSquare.sg10400`, `OAI.UniversalTensorSquare.sg10401`, `OAI.UniversalTensorSquare.sg10402`, `OAI.UniversalTensorSquare.sg10403`, `OAI.UniversalTensorSquare.sg10405`, `OAI.UniversalTensorSquare.sg10406`, `OAI.UniversalTensorSquare.sg10407`, `OAI.UniversalTensorSquare.sg10408`, `OAI.UniversalTensorSquare.sg10409`, `OAI.UniversalTensorSquare.sg10410`, `OAI.UniversalTensorSquare.sg10472`, `OAI.UniversalTensorSquare.sg10475`, `OAI.UniversalTensorSquare.sg10476`, `OAI.UniversalTensorSquare.sg10479`, `OAI.UniversalTensorSquare.sg10480`, `OAI.UniversalTensorSquare.sg10488`, `OAI.UniversalTensorSquare.sg10489`, `OAI.UniversalTensorSquare.sg10491`, `OAI.UniversalTensorSquare.sg10492`, `OAI.UniversalTensorSquare.sg10494`, `OAI.UniversalTensorSquare.sg10495`, `OAI.UniversalTensorSquare.sg10498`, `OAI.UniversalTensorSquare.sg10500`, `OAI.UniversalTensorSquare.sg10501`, `OAI.UniversalTensorSquare.sg10537`, `OAI.UniversalTensorSquare.sg10624`, `OAI.UniversalTensorSquare.sg10634`, `OAI.UniversalTensorSquare.sg10639`, `OAI.UniversalTensorSquare.sg10664`, `OAI.UniversalTensorSquare.sg10666`, `OAI.UniversalTensorSquare.sg10676`, `OAI.UniversalTensorSquare.sg10686`, `OAI.UniversalTensorSquare.sg10689`, `OAI.UniversalTensorSquare.sg10916`, `OAI.UniversalTensorSquare.sg10918`, `OAI.UniversalTensorSquare.sg10946`, `OAI.UniversalTensorSquare.sg10949`, `OAI.UniversalTensorSquare.sg10963`, `OAI.UniversalTensorSquare.sg10972`, `OAI.UniversalTensorSquare.sg10977`, `OAI.UniversalTensorSquare.sg10980`, `OAI.UniversalTensorSquare.sg10981`, `OAI.UniversalTensorSquare.sg10984`, `OAI.UniversalTensorSquare.sg11010`, `OAI.UniversalTensorSquare.sg11208`, `OAI.UniversalTensorSquare.sg11209`, `OAI.UniversalTensorSquare.sg11210`, `OAI.UniversalTensorSquare.sg11212`, `OAI.UniversalTensorSquare.sg11213`, `OAI.UniversalTensorSquare.sg11215`, `OAI.UniversalTensorSquare.sg11226`, `OAI.UniversalTensorSquare.sg11227`, `OAI.UniversalTensorSquare.sg11228`, `OAI.UniversalTensorSquare.sg11229`, `OAI.UniversalTensorSquare.sg11230`, `OAI.UniversalTensorSquare.sg11231`, `OAI.UniversalTensorSquare.sg11232`, `OAI.UniversalTensorSquare.sg11233`, `OAI.UniversalTensorSquare.sg11234`, `OAI.UniversalTensorSquare.sg11278`, `OAI.UniversalTensorSquare.sg11280`, `OAI.UniversalTensorSquare.sg11304`, `OAI.UniversalTensorSquare.sg11307`, `OAI.UniversalTensorSquare.sg11496`, `OAI.UniversalTensorSquare.sg11497`, `OAI.UniversalTensorSquare.sg11498`, `OAI.UniversalTensorSquare.sg11499`, `OAI.UniversalTensorSquare.sg11500`, `OAI.UniversalTensorSquare.sg11501`, `OAI.UniversalTensorSquare.sg11502`, `OAI.UniversalTensorSquare.sg1162`, `OAI.UniversalTensorSquare.sg1169`, `OAI.UniversalTensorSquare.sg11842`, `OAI.UniversalTensorSquare.sg11843`, `OAI.UniversalTensorSquare.sg11848`, `OAI.UniversalTensorSquare.sg11852`, `OAI.UniversalTensorSquare.sg11855`, `OAI.UniversalTensorSquare.sg11868`, `OAI.UniversalTensorSquare.sg11869`, `OAI.UniversalTensorSquare.sg11903`, `OAI.UniversalTensorSquare.sg11925`, `OAI.UniversalTensorSquare.sg11929`, `OAI.UniversalTensorSquare.sg11930`, `OAI.UniversalTensorSquare.sg11951`, `OAI.UniversalTensorSquare.sg11971`, `OAI.UniversalTensorSquare.sg11973`, `OAI.UniversalTensorSquare.sg11980`, `OAI.UniversalTensorSquare.sg11985`, `OAI.UniversalTensorSquare.sg11989`, `OAI.UniversalTensorSquare.sg11990`, `OAI.UniversalTensorSquare.sg11992`, `OAI.UniversalTensorSquare.sg12001`, `OAI.UniversalTensorSquare.sg12003`, `OAI.UniversalTensorSquare.sg12007`, `OAI.UniversalTensorSquare.sg12015`, `OAI.UniversalTensorSquare.sg12023`, `OAI.UniversalTensorSquare.sg12033`, `OAI.UniversalTensorSquare.sg12037`, `OAI.UniversalTensorSquare.sg12040`, `OAI.UniversalTensorSquare.sg12042`, `OAI.UniversalTensorSquare.sg12048`, `OAI.UniversalTensorSquare.sg12059`, `OAI.UniversalTensorSquare.sg12060`, `OAI.UniversalTensorSquare.sg12081`, `OAI.UniversalTensorSquare.sg12082`, `OAI.UniversalTensorSquare.sg12101`, `OAI.UniversalTensorSquare.sg12119`, `OAI.UniversalTensorSquare.sg12132`, `OAI.UniversalTensorSquare.sg12160`, `OAI.UniversalTensorSquare.sg12164`, `OAI.UniversalTensorSquare.sg12180`, `OAI.UniversalTensorSquare.sg12184`, `OAI.UniversalTensorSquare.sg12185`, `OAI.UniversalTensorSquare.sg12187`, `OAI.UniversalTensorSquare.sg12223`, `OAI.UniversalTensorSquare.sg12232`, `OAI.UniversalTensorSquare.sg12245`, `OAI.UniversalTensorSquare.sg12251`, `OAI.UniversalTensorSquare.sg12293`, `OAI.UniversalTensorSquare.sg12418`, `OAI.UniversalTensorSquare.sg13084`, `OAI.UniversalTensorSquare.sg13104`, `OAI.UniversalTensorSquare.sg13121`, `OAI.UniversalTensorSquare.sg13141`, `OAI.UniversalTensorSquare.sg13305`, `OAI.UniversalTensorSquare.sg13307`, `OAI.UniversalTensorSquare.sg13353`, `OAI.UniversalTensorSquare.sg13354`, `OAI.UniversalTensorSquare.sg13363`, `OAI.UniversalTensorSquare.sg13416`, `OAI.UniversalTensorSquare.sg13480`, `OAI.UniversalTensorSquare.sg14235`, `OAI.UniversalTensorSquare.sg14296`, `OAI.UniversalTensorSquare.sg14386`, `OAI.UniversalTensorSquare.sg14640`, `OAI.UniversalTensorSquare.sg14756`, `OAI.UniversalTensorSquare.sg14762`, `OAI.UniversalTensorSquare.sg14763`, `OAI.UniversalTensorSquare.sg14812`, `OAI.UniversalTensorSquare.sg14816`, `OAI.UniversalTensorSquare.sg15756`, `OAI.UniversalTensorSquare.sg15886`, `OAI.UniversalTensorSquare.sg15936`, `OAI.UniversalTensorSquare.sg16165`, `OAI.UniversalTensorSquare.sg16341`, `OAI.UniversalTensorSquare.sg16364`, `OAI.UniversalTensorSquare.sg16379`, `OAI.UniversalTensorSquare.sg16731`, `OAI.UniversalTensorSquare.sg17188`, `OAI.UniversalTensorSquare.sg17197`, `OAI.UniversalTensorSquare.sg17298`, `OAI.UniversalTensorSquare.sg17299`, `OAI.UniversalTensorSquare.sg17341`, `OAI.UniversalTensorSquare.sg17342`, `OAI.UniversalTensorSquare.sg17475`, `OAI.UniversalTensorSquare.sg17542`, `OAI.UniversalTensorSquare.sg17754`, `OAI.UniversalTensorSquare.sg18703`, `OAI.UniversalTensorSquare.sg18762`, `OAI.UniversalTensorSquare.sg18846`, `OAI.UniversalTensorSquare.sg18971`, `OAI.UniversalTensorSquare.sg18974`, `OAI.UniversalTensorSquare.sg19133`, `OAI.UniversalTensorSquare.sg19153`, `OAI.UniversalTensorSquare.sg19171`, `OAI.UniversalTensorSquare.sg19321`, `OAI.UniversalTensorSquare.sg19623`, `OAI.UniversalTensorSquare.sg19628`, `OAI.UniversalTensorSquare.sg19635`, `OAI.UniversalTensorSquare.sg19709`, `OAI.UniversalTensorSquare.sg19710`, `OAI.UniversalTensorSquare.sg20306`, `OAI.UniversalTensorSquare.sg20588`, `OAI.UniversalTensorSquare.sg20660`, `OAI.UniversalTensorSquare.sg20661`, `OAI.UniversalTensorSquare.sg20674`, `OAI.UniversalTensorSquare.sg20675`, `OAI.UniversalTensorSquare.sg20676`, `OAI.UniversalTensorSquare.sg20677`, `OAI.UniversalTensorSquare.sg20680`, `OAI.UniversalTensorSquare.sg20682`, `OAI.UniversalTensorSquare.sg20758`, `OAI.UniversalTensorSquare.sg20787`, `OAI.UniversalTensorSquare.sg20788`, `OAI.UniversalTensorSquare.sg21085`, `OAI.UniversalTensorSquare.sg21086`, `OAI.UniversalTensorSquare.sg21087`, `OAI.UniversalTensorSquare.sg21349`, `OAI.UniversalTensorSquare.sg21351`, `OAI.UniversalTensorSquare.sg21356`, `OAI.UniversalTensorSquare.sg21359`, `OAI.UniversalTensorSquare.sg21401`, `OAI.UniversalTensorSquare.sg21402`, `OAI.UniversalTensorSquare.sg21405`, `OAI.UniversalTensorSquare.sg21406`, `OAI.UniversalTensorSquare.sg21410`, `OAI.UniversalTensorSquare.sg21505`, `OAI.UniversalTensorSquare.sg21516`, `OAI.UniversalTensorSquare.sg21557`, `OAI.UniversalTensorSquare.sg21565`, `OAI.UniversalTensorSquare.sg21596`, `OAI.UniversalTensorSquare.sg21607`, `OAI.UniversalTensorSquare.sg21671`, `OAI.UniversalTensorSquare.sg21697`, `OAI.UniversalTensorSquare.sg21701`, `OAI.UniversalTensorSquare.sg21706`, `OAI.UniversalTensorSquare.sg21707`, `OAI.UniversalTensorSquare.sg21710`, `OAI.UniversalTensorSquare.sg21712`, `OAI.UniversalTensorSquare.sg21716`, `OAI.UniversalTensorSquare.sg21737`, `OAI.UniversalTensorSquare.sg21745`, `OAI.UniversalTensorSquare.sg21748`, `OAI.UniversalTensorSquare.sg21757`, `OAI.UniversalTensorSquare.sg21763`, `OAI.UniversalTensorSquare.sg21766`, `OAI.UniversalTensorSquare.sg21772`, `OAI.UniversalTensorSquare.sg21777`, `OAI.UniversalTensorSquare.sg21778`, `OAI.UniversalTensorSquare.sg21782`, `OAI.UniversalTensorSquare.sg21784`, `OAI.UniversalTensorSquare.sg21789`, `OAI.UniversalTensorSquare.sg21791`, `OAI.UniversalTensorSquare.sg21793`, `OAI.UniversalTensorSquare.sg21794`, `OAI.UniversalTensorSquare.sg21801`, `OAI.UniversalTensorSquare.sg21803`, `OAI.UniversalTensorSquare.sg21810`, `OAI.UniversalTensorSquare.sg21812`, `OAI.UniversalTensorSquare.sg21817`, `OAI.UniversalTensorSquare.sg21821`, `OAI.UniversalTensorSquare.sg21823`, `OAI.UniversalTensorSquare.sg21829`, `OAI.UniversalTensorSquare.sg21833`, `OAI.UniversalTensorSquare.sg21835`, `OAI.UniversalTensorSquare.sg21839`, `OAI.UniversalTensorSquare.sg21870`, `OAI.UniversalTensorSquare.sg21878`, `OAI.UniversalTensorSquare.sg21880`, `OAI.UniversalTensorSquare.sg21883`, `OAI.UniversalTensorSquare.sg21884`, `OAI.UniversalTensorSquare.sg21887`, `OAI.UniversalTensorSquare.sg21888`, `OAI.UniversalTensorSquare.sg21897`, `OAI.UniversalTensorSquare.sg21900`, `OAI.UniversalTensorSquare.sg21901`, `OAI.UniversalTensorSquare.sg21902`, `OAI.UniversalTensorSquare.sg21905`, `OAI.UniversalTensorSquare.sg21907`, `OAI.UniversalTensorSquare.sg21908`, `OAI.UniversalTensorSquare.sg21909`, `OAI.UniversalTensorSquare.sg21911`, `OAI.UniversalTensorSquare.sg21913`, `OAI.UniversalTensorSquare.sg21915`, `OAI.UniversalTensorSquare.sg21918`, `OAI.UniversalTensorSquare.sg21920`, `OAI.UniversalTensorSquare.sg21921`, `OAI.UniversalTensorSquare.sg21922`, `OAI.UniversalTensorSquare.sg21923`, `OAI.UniversalTensorSquare.sg21924`, `OAI.UniversalTensorSquare.sg21928`, `OAI.UniversalTensorSquare.sg21930`, `OAI.UniversalTensorSquare.sg21931`, `OAI.UniversalTensorSquare.sg21934`, `OAI.UniversalTensorSquare.sg21936`, `OAI.UniversalTensorSquare.sg21938`, `OAI.UniversalTensorSquare.sg21940`, `OAI.UniversalTensorSquare.sg21942`, `OAI.UniversalTensorSquare.sg21944`, `OAI.UniversalTensorSquare.sg21947`, `OAI.UniversalTensorSquare.sg21952`, `OAI.UniversalTensorSquare.sg21955`, `OAI.UniversalTensorSquare.sg21956`, `OAI.UniversalTensorSquare.sg21957`, `OAI.UniversalTensorSquare.sg21958`, `OAI.UniversalTensorSquare.sg21960`, `OAI.UniversalTensorSquare.sg21962`, `OAI.UniversalTensorSquare.sg21963`, `OAI.UniversalTensorSquare.sg21967`, `OAI.UniversalTensorSquare.sg21968`, `OAI.UniversalTensorSquare.sg21969`, `OAI.UniversalTensorSquare.sg21972`, `OAI.UniversalTensorSquare.sg21973`, `OAI.UniversalTensorSquare.sg21974`, `OAI.UniversalTensorSquare.sg21975`, `OAI.UniversalTensorSquare.sg21982`, `OAI.UniversalTensorSquare.sg21983`, `OAI.UniversalTensorSquare.sg21985`, `OAI.UniversalTensorSquare.sg21987`, `OAI.UniversalTensorSquare.sg21989`, `OAI.UniversalTensorSquare.sg21992`, `OAI.UniversalTensorSquare.sg21994`, `OAI.UniversalTensorSquare.sg21995`, `OAI.UniversalTensorSquare.sg22000`, `OAI.UniversalTensorSquare.sg22003`, `OAI.UniversalTensorSquare.sg22005`, `OAI.UniversalTensorSquare.sg22006`, `OAI.UniversalTensorSquare.sg22008`, `OAI.UniversalTensorSquare.sg22009`, `OAI.UniversalTensorSquare.sg22011`, `OAI.UniversalTensorSquare.sg22012`, `OAI.UniversalTensorSquare.sg22015`, `OAI.UniversalTensorSquare.sg22018`, `OAI.UniversalTensorSquare.sg22021`, `OAI.UniversalTensorSquare.sg22022`, `OAI.UniversalTensorSquare.sg22031`, `OAI.UniversalTensorSquare.sg22035`, `OAI.UniversalTensorSquare.sg22037`, `OAI.UniversalTensorSquare.sg22038`, `OAI.UniversalTensorSquare.sg22040`, `OAI.UniversalTensorSquare.sg22046`, `OAI.UniversalTensorSquare.sg22049`, `OAI.UniversalTensorSquare.sg22050`, `OAI.UniversalTensorSquare.sg22053`, `OAI.UniversalTensorSquare.sg22057`, `OAI.UniversalTensorSquare.sg22059`, `OAI.UniversalTensorSquare.sg22061`, `OAI.UniversalTensorSquare.sg22063`, `OAI.UniversalTensorSquare.sg22065`, `OAI.UniversalTensorSquare.sg22067`, `OAI.UniversalTensorSquare.sg22068`, `OAI.UniversalTensorSquare.sg22069`, `OAI.UniversalTensorSquare.sg22072`, `OAI.UniversalTensorSquare.sg22073`, `OAI.UniversalTensorSquare.sg22074`, `OAI.UniversalTensorSquare.sg22075`, `OAI.UniversalTensorSquare.sg22076`, `OAI.UniversalTensorSquare.sg22079`, `OAI.UniversalTensorSquare.sg22080`, `OAI.UniversalTensorSquare.sg22082`, `OAI.UniversalTensorSquare.sg22088`, `OAI.UniversalTensorSquare.sg22101`, `OAI.UniversalTensorSquare.sg22118`, `OAI.UniversalTensorSquare.sg22121`, `OAI.UniversalTensorSquare.sg22122`, `OAI.UniversalTensorSquare.sg22151`, `OAI.UniversalTensorSquare.sg22158`, `OAI.UniversalTensorSquare.sg22159`, `OAI.UniversalTensorSquare.sg22163`, `OAI.UniversalTensorSquare.sg22168`, `OAI.UniversalTensorSquare.sg22171`, `OAI.UniversalTensorSquare.sg22174`, `OAI.UniversalTensorSquare.sg22195`, `OAI.UniversalTensorSquare.sg22196`, `OAI.UniversalTensorSquare.sg22198`, `OAI.UniversalTensorSquare.sg22199`, `OAI.UniversalTensorSquare.sg22200`, `OAI.UniversalTensorSquare.sg22201`, `OAI.UniversalTensorSquare.sg22219`, `OAI.UniversalTensorSquare.sg22233`, `OAI.UniversalTensorSquare.sg22234`, `OAI.UniversalTensorSquare.sg22238`, `OAI.UniversalTensorSquare.sg22239`, `OAI.UniversalTensorSquare.sg22243`, `OAI.UniversalTensorSquare.sg22245`, `OAI.UniversalTensorSquare.sg22248`, `OAI.UniversalTensorSquare.sg22250`, `OAI.UniversalTensorSquare.sg22251`, `OAI.UniversalTensorSquare.sg22253`, `OAI.UniversalTensorSquare.sg22255`, `OAI.UniversalTensorSquare.sg22256`, `OAI.UniversalTensorSquare.sg22261`, `OAI.UniversalTensorSquare.sg22266`, `OAI.UniversalTensorSquare.sg22267`, `OAI.UniversalTensorSquare.sg22270`, `OAI.UniversalTensorSquare.sg22271`, `OAI.UniversalTensorSquare.sg22272`, `OAI.UniversalTensorSquare.sg22278`, `OAI.UniversalTensorSquare.sg22279`, `OAI.UniversalTensorSquare.sg22282`, `OAI.UniversalTensorSquare.sg22283`, `OAI.UniversalTensorSquare.sg22284`, `OAI.UniversalTensorSquare.sg22285`, `OAI.UniversalTensorSquare.sg22290`, `OAI.UniversalTensorSquare.sg22291`, `OAI.UniversalTensorSquare.sg22305`, `OAI.UniversalTensorSquare.sg22308`, `OAI.UniversalTensorSquare.sg22333`, `OAI.UniversalTensorSquare.sg22336`, `OAI.UniversalTensorSquare.sg22342`, `OAI.UniversalTensorSquare.sg22346`, `OAI.UniversalTensorSquare.sg22347`, `OAI.UniversalTensorSquare.sg22348`, `OAI.UniversalTensorSquare.sg22349`, `OAI.UniversalTensorSquare.sg22351`, `OAI.UniversalTensorSquare.sg22353`, `OAI.UniversalTensorSquare.sg22355`, `OAI.UniversalTensorSquare.sg22361`, `OAI.UniversalTensorSquare.sg22363`, `OAI.UniversalTensorSquare.sg22364`, `OAI.UniversalTensorSquare.sg22365`, `OAI.UniversalTensorSquare.sg22366`, `OAI.UniversalTensorSquare.sg22370`, `OAI.UniversalTensorSquare.sg22374`, `OAI.UniversalTensorSquare.sg22378`, `OAI.UniversalTensorSquare.sg22380`, `OAI.UniversalTensorSquare.sg22381`, `OAI.UniversalTensorSquare.sg22383`, `OAI.UniversalTensorSquare.sg22384`, `OAI.UniversalTensorSquare.sg22385`, `OAI.UniversalTensorSquare.sg22386`, `OAI.UniversalTensorSquare.sg22399`, `OAI.UniversalTensorSquare.sg22412`, `OAI.UniversalTensorSquare.sg22499`, `OAI.UniversalTensorSquare.sg22567`, `OAI.UniversalTensorSquare.sg22584`, `OAI.UniversalTensorSquare.sg22586`, `OAI.UniversalTensorSquare.sg22592`, `OAI.UniversalTensorSquare.sg22646`, `OAI.UniversalTensorSquare.sg22704`, `OAI.UniversalTensorSquare.sg22708`, `OAI.UniversalTensorSquare.sg22716`, `OAI.UniversalTensorSquare.sg22731`, `OAI.UniversalTensorSquare.sg22786`, `OAI.UniversalTensorSquare.sg22803`, `OAI.UniversalTensorSquare.sg22811`, `OAI.UniversalTensorSquare.sg22821`, `OAI.UniversalTensorSquare.sg22823`, `OAI.UniversalTensorSquare.sg22842`, `OAI.UniversalTensorSquare.sg22845`, `OAI.UniversalTensorSquare.sg22851`, `OAI.UniversalTensorSquare.sg22857`, `OAI.UniversalTensorSquare.sg22867`, `OAI.UniversalTensorSquare.sg22881`, `OAI.UniversalTensorSquare.sg22882`, `OAI.UniversalTensorSquare.sg22884`, `OAI.UniversalTensorSquare.sg22890`, `OAI.UniversalTensorSquare.sg22900`, `OAI.UniversalTensorSquare.sg22914`, `OAI.UniversalTensorSquare.sg22917`, `OAI.UniversalTensorSquare.sg22922`, `OAI.UniversalTensorSquare.sg22941`, `OAI.UniversalTensorSquare.sg22943`, `OAI.UniversalTensorSquare.sg22955`, `OAI.UniversalTensorSquare.sg22976`, `OAI.UniversalTensorSquare.sg22977`, `OAI.UniversalTensorSquare.sg22983`, `OAI.UniversalTensorSquare.sg23000`, `OAI.UniversalTensorSquare.sg23021`, `OAI.UniversalTensorSquare.sg23024`, `OAI.UniversalTensorSquare.sg23031`, `OAI.UniversalTensorSquare.sg23032`, `OAI.UniversalTensorSquare.sg23038`, `OAI.UniversalTensorSquare.sg23057`, `OAI.UniversalTensorSquare.sg23082`, `OAI.UniversalTensorSquare.sg23087`, `OAI.UniversalTensorSquare.sg23096`, `OAI.UniversalTensorSquare.sg23105`, `OAI.UniversalTensorSquare.sg23110`, `OAI.UniversalTensorSquare.sg23122`, `OAI.UniversalTensorSquare.sg23123`, `OAI.UniversalTensorSquare.sg23129`, `OAI.UniversalTensorSquare.sg23197`, `OAI.UniversalTensorSquare.sg23221`, `OAI.UniversalTensorSquare.sg23231`, `OAI.UniversalTensorSquare.sg23232`, `OAI.UniversalTensorSquare.sg23234`, `OAI.UniversalTensorSquare.sg23235`, `OAI.UniversalTensorSquare.sg23238`, `OAI.UniversalTensorSquare.sg23239`, `OAI.UniversalTensorSquare.sg23245`, `OAI.UniversalTensorSquare.sg23252`, `OAI.UniversalTensorSquare.sg23253`, `OAI.UniversalTensorSquare.sg23259`, `OAI.UniversalTensorSquare.sg23268`, `OAI.UniversalTensorSquare.sg23281`, `OAI.UniversalTensorSquare.sg23282`, `OAI.UniversalTensorSquare.sg23289`, `OAI.UniversalTensorSquare.sg23290`, `OAI.UniversalTensorSquare.sg23295`, `OAI.UniversalTensorSquare.sg23314`, `OAI.UniversalTensorSquare.sg23315`, `OAI.UniversalTensorSquare.sg23318`, `OAI.UniversalTensorSquare.sg23321`, `OAI.UniversalTensorSquare.sg23324`, `OAI.UniversalTensorSquare.sg23339`, `OAI.UniversalTensorSquare.sg23344`, `OAI.UniversalTensorSquare.sg23408`, `OAI.UniversalTensorSquare.sg23419`, `OAI.UniversalTensorSquare.sg23423`, `OAI.UniversalTensorSquare.sg23424`, `OAI.UniversalTensorSquare.sg23434`, `OAI.UniversalTensorSquare.sg23440`, `OAI.UniversalTensorSquare.sg23441`, `OAI.UniversalTensorSquare.sg23447`, `OAI.UniversalTensorSquare.sg23448`, `OAI.UniversalTensorSquare.sg23451`, `OAI.UniversalTensorSquare.sg23463`, `OAI.UniversalTensorSquare.sg23464`, `OAI.UniversalTensorSquare.sg23468`, `OAI.UniversalTensorSquare.sg23479`, `OAI.UniversalTensorSquare.sg23481`, `OAI.UniversalTensorSquare.sg23487`, `OAI.UniversalTensorSquare.sg23496`, `OAI.UniversalTensorSquare.sg23500`, `OAI.UniversalTensorSquare.sg23509`, `OAI.UniversalTensorSquare.sg23510`, `OAI.UniversalTensorSquare.sg23525`, `OAI.UniversalTensorSquare.sg23528`, `OAI.UniversalTensorSquare.sg23529`, `OAI.UniversalTensorSquare.sg23566`, `OAI.UniversalTensorSquare.sg23569`, `OAI.UniversalTensorSquare.sg23573`, `OAI.UniversalTensorSquare.sg23578`, `OAI.UniversalTensorSquare.sg23583`, `OAI.UniversalTensorSquare.sg23586`, `OAI.UniversalTensorSquare.sg23593`, `OAI.UniversalTensorSquare.sg23595`, `OAI.UniversalTensorSquare.sg23599`, `OAI.UniversalTensorSquare.sg23600`, `OAI.UniversalTensorSquare.sg23606`, `OAI.UniversalTensorSquare.sg23608`, `OAI.UniversalTensorSquare.sg23610`, `OAI.UniversalTensorSquare.sg23611`, `OAI.UniversalTensorSquare.sg23620`, `OAI.UniversalTensorSquare.sg23623`, `OAI.UniversalTensorSquare.sg23627`, `OAI.UniversalTensorSquare.sg23630`, `OAI.UniversalTensorSquare.sg23632`, `OAI.UniversalTensorSquare.sg23634`, `OAI.UniversalTensorSquare.sg23635`, `OAI.UniversalTensorSquare.sg23636`, `OAI.UniversalTensorSquare.sg23637`, `OAI.UniversalTensorSquare.sg23657`, `OAI.UniversalTensorSquare.sg23658`, `OAI.UniversalTensorSquare.sg23663`, `OAI.UniversalTensorSquare.sg23670`, `OAI.UniversalTensorSquare.sg23677`, `OAI.UniversalTensorSquare.sg23680`, `OAI.UniversalTensorSquare.sg23681`, `OAI.UniversalTensorSquare.sg23682`, `OAI.UniversalTensorSquare.sg23683`, `OAI.UniversalTensorSquare.sg23684`, `OAI.UniversalTensorSquare.sg23687`, `OAI.UniversalTensorSquare.sg23689`, `OAI.UniversalTensorSquare.sg23690`, `OAI.UniversalTensorSquare.sg23691`, `OAI.UniversalTensorSquare.sg23692`, `OAI.UniversalTensorSquare.sg23710`, `OAI.UniversalTensorSquare.sg23729`, `OAI.UniversalTensorSquare.sg23744`, `OAI.UniversalTensorSquare.sg23766`, `OAI.UniversalTensorSquare.sg23780`, `OAI.UniversalTensorSquare.sg23785`, `OAI.UniversalTensorSquare.sg23794`, `OAI.UniversalTensorSquare.sg23798`, `OAI.UniversalTensorSquare.sg23800`, `OAI.UniversalTensorSquare.sg23808`, `OAI.UniversalTensorSquare.sg23809`, `OAI.UniversalTensorSquare.sg23815`, `OAI.UniversalTensorSquare.sg23816`, `OAI.UniversalTensorSquare.sg23819`, `OAI.UniversalTensorSquare.sg23820`, `OAI.UniversalTensorSquare.sg23823`, `OAI.UniversalTensorSquare.sg23826`, `OAI.UniversalTensorSquare.sg23838`, `OAI.UniversalTensorSquare.sg23840`, `OAI.UniversalTensorSquare.sg23842`, `OAI.UniversalTensorSquare.sg23880`, `OAI.UniversalTensorSquare.sg23883`, `OAI.UniversalTensorSquare.sg23889`, `OAI.UniversalTensorSquare.sg23893`, `OAI.UniversalTensorSquare.sg23902`, `OAI.UniversalTensorSquare.sg23907`, `OAI.UniversalTensorSquare.sg23923`, `OAI.UniversalTensorSquare.sg23935`, `OAI.UniversalTensorSquare.sg23936`, `OAI.UniversalTensorSquare.sg23938`, `OAI.UniversalTensorSquare.sg23940`, `OAI.UniversalTensorSquare.sg23941`, `OAI.UniversalTensorSquare.sg23954`, `OAI.UniversalTensorSquare.sg23964`, `OAI.UniversalTensorSquare.sg23970`, `OAI.UniversalTensorSquare.sg23981`, `OAI.UniversalTensorSquare.sg23994`, `OAI.UniversalTensorSquare.sg23996`, `OAI.UniversalTensorSquare.sg24008`, `OAI.UniversalTensorSquare.sg24010`, `OAI.UniversalTensorSquare.sg24019`, `OAI.UniversalTensorSquare.sg24022`, `OAI.UniversalTensorSquare.sg24024`, `OAI.UniversalTensorSquare.sg24036`, `OAI.UniversalTensorSquare.sg24040`, `OAI.UniversalTensorSquare.sg24041`, `OAI.UniversalTensorSquare.sg24048`, `OAI.UniversalTensorSquare.sg24049`, `OAI.UniversalTensorSquare.sg24052`, `OAI.UniversalTensorSquare.sg24054`, `OAI.UniversalTensorSquare.sg24067`, `OAI.UniversalTensorSquare.sg24069`, `OAI.UniversalTensorSquare.sg24070`, `OAI.UniversalTensorSquare.sg24073`, `OAI.UniversalTensorSquare.sg24087`, `OAI.UniversalTensorSquare.sg24104`, `OAI.UniversalTensorSquare.sg24107`, `OAI.UniversalTensorSquare.sg24116`, `OAI.UniversalTensorSquare.sg24121`, `OAI.UniversalTensorSquare.sg24126`, `OAI.UniversalTensorSquare.sg24136`, `OAI.UniversalTensorSquare.sg24139`, `OAI.UniversalTensorSquare.sg24140`, `OAI.UniversalTensorSquare.sg24144`, `OAI.UniversalTensorSquare.sg24149`, `OAI.UniversalTensorSquare.sg24150`, `OAI.UniversalTensorSquare.sg24153`, `OAI.UniversalTensorSquare.sg24154`, `OAI.UniversalTensorSquare.sg24155`, `OAI.UniversalTensorSquare.sg24157`, `OAI.UniversalTensorSquare.sg24158`, `OAI.UniversalTensorSquare.sg24160`, `OAI.UniversalTensorSquare.sg24166`, `OAI.UniversalTensorSquare.sg24167`, `OAI.UniversalTensorSquare.sg24169`, `OAI.UniversalTensorSquare.sg24171`, `OAI.UniversalTensorSquare.sg24174`, `OAI.UniversalTensorSquare.sg24183`, `OAI.UniversalTensorSquare.sg24185`, `OAI.UniversalTensorSquare.sg24188`, `OAI.UniversalTensorSquare.sg24192`, `OAI.UniversalTensorSquare.sg24194`, `OAI.UniversalTensorSquare.sg24196`, `OAI.UniversalTensorSquare.sg24197`, `OAI.UniversalTensorSquare.sg24200`, `OAI.UniversalTensorSquare.sg24203`, `OAI.UniversalTensorSquare.sg24209`, `OAI.UniversalTensorSquare.sg24210`, `OAI.UniversalTensorSquare.sg24212`, `OAI.UniversalTensorSquare.sg24217`, `OAI.UniversalTensorSquare.sg24227`, `OAI.UniversalTensorSquare.sg24257`, `OAI.UniversalTensorSquare.sg24270`, `OAI.UniversalTensorSquare.sg24275`, `OAI.UniversalTensorSquare.sg24281`, `OAI.UniversalTensorSquare.sg24285`, `OAI.UniversalTensorSquare.sg24292`, `OAI.UniversalTensorSquare.sg24296`, `OAI.UniversalTensorSquare.sg24303`, `OAI.UniversalTensorSquare.sg24308`, `OAI.UniversalTensorSquare.sg24310`, `OAI.UniversalTensorSquare.sg24313`, `OAI.UniversalTensorSquare.sg24315`, `OAI.UniversalTensorSquare.sg24321`, `OAI.UniversalTensorSquare.sg24330`, `OAI.UniversalTensorSquare.sg24339`, `OAI.UniversalTensorSquare.sg24347`, `OAI.UniversalTensorSquare.sg24354`, `OAI.UniversalTensorSquare.sg24355`, `OAI.UniversalTensorSquare.sg24356`, `OAI.UniversalTensorSquare.sg24361`, `OAI.UniversalTensorSquare.sg24367`, `OAI.UniversalTensorSquare.sg24376`, `OAI.UniversalTensorSquare.sg24378`, `OAI.UniversalTensorSquare.sg24379`, `OAI.UniversalTensorSquare.sg24380`, `OAI.UniversalTensorSquare.sg24385`, `OAI.UniversalTensorSquare.sg24389`, `OAI.UniversalTensorSquare.sg24408`, `OAI.UniversalTensorSquare.sg24415`, `OAI.UniversalTensorSquare.sg24417`, `OAI.UniversalTensorSquare.sg24423`, `OAI.UniversalTensorSquare.sg24424`, `OAI.UniversalTensorSquare.sg24425`, `OAI.UniversalTensorSquare.sg24432`, `OAI.UniversalTensorSquare.sg24438`, `OAI.UniversalTensorSquare.sg24439`, `OAI.UniversalTensorSquare.sg24446`, `OAI.UniversalTensorSquare.sg24448`, `OAI.UniversalTensorSquare.sg24450`, `OAI.UniversalTensorSquare.sg24451`, `OAI.UniversalTensorSquare.sg24452`, `OAI.UniversalTensorSquare.sg24453`, `OAI.UniversalTensorSquare.sg24467`, `OAI.UniversalTensorSquare.sg24469`, `OAI.UniversalTensorSquare.sg24470`, `OAI.UniversalTensorSquare.sg24471`, `OAI.UniversalTensorSquare.sg24479`, `OAI.UniversalTensorSquare.sg24481`, `OAI.UniversalTensorSquare.sg24483`, `OAI.UniversalTensorSquare.sg24495`, `OAI.UniversalTensorSquare.sg24497`, `OAI.UniversalTensorSquare.sg24502`, `OAI.UniversalTensorSquare.sg24504`, `OAI.UniversalTensorSquare.sg24505`, `OAI.UniversalTensorSquare.sg24506`, `OAI.UniversalTensorSquare.sg24508`, `OAI.UniversalTensorSquare.sg24509`, `OAI.UniversalTensorSquare.sg24516`, `OAI.UniversalTensorSquare.sg24518`, `OAI.UniversalTensorSquare.sg24522`, `OAI.UniversalTensorSquare.sg24526`, `OAI.UniversalTensorSquare.sg24529`, `OAI.UniversalTensorSquare.sg24532`, `OAI.UniversalTensorSquare.sg24535`, `OAI.UniversalTensorSquare.sg24537`, `OAI.UniversalTensorSquare.sg24539`, `OAI.UniversalTensorSquare.sg24540`, `OAI.UniversalTensorSquare.sg24541`, `OAI.UniversalTensorSquare.sg24545`, `OAI.UniversalTensorSquare.sg24547`, `OAI.UniversalTensorSquare.sg24551`, `OAI.UniversalTensorSquare.sg24552`, `OAI.UniversalTensorSquare.sg24557`, `OAI.UniversalTensorSquare.sg24558`, `OAI.UniversalTensorSquare.sg24559`, `OAI.UniversalTensorSquare.sg24560`, `OAI.UniversalTensorSquare.sg24562`, `OAI.UniversalTensorSquare.sg24564`, `OAI.UniversalTensorSquare.sg24566`, `OAI.UniversalTensorSquare.sg24567`, `OAI.UniversalTensorSquare.sg24568`, `OAI.UniversalTensorSquare.sg24571`, `OAI.UniversalTensorSquare.sg24573`, `OAI.UniversalTensorSquare.sg24576`, `OAI.UniversalTensorSquare.sg24577`, `OAI.UniversalTensorSquare.sg24579`, `OAI.UniversalTensorSquare.sg24586`, `OAI.UniversalTensorSquare.sg24587`, `OAI.UniversalTensorSquare.sg24592`, `OAI.UniversalTensorSquare.sg24596`, `OAI.UniversalTensorSquare.sg24599`, `OAI.UniversalTensorSquare.sg24602`, `OAI.UniversalTensorSquare.sg24609`, `OAI.UniversalTensorSquare.sg24612`, `OAI.UniversalTensorSquare.sg24614`, `OAI.UniversalTensorSquare.sg24622`, `OAI.UniversalTensorSquare.sg24623`, `OAI.UniversalTensorSquare.sg24627`, `OAI.UniversalTensorSquare.sg24628`, `OAI.UniversalTensorSquare.sg24630`, `OAI.UniversalTensorSquare.sg24633`, `OAI.UniversalTensorSquare.sg24635`, `OAI.UniversalTensorSquare.sg24636`, `OAI.UniversalTensorSquare.sg24637`, `OAI.UniversalTensorSquare.sg24638`, `OAI.UniversalTensorSquare.sg24639`, `OAI.UniversalTensorSquare.sg24644`, `OAI.UniversalTensorSquare.sg24646`, `OAI.UniversalTensorSquare.sg24648`, `OAI.UniversalTensorSquare.sg24649`, `OAI.UniversalTensorSquare.sg24650`, `OAI.UniversalTensorSquare.sg24652`, `OAI.UniversalTensorSquare.sg24653`, `OAI.UniversalTensorSquare.sg24654`, `OAI.UniversalTensorSquare.sg24655`, `OAI.UniversalTensorSquare.sg24656`, `OAI.UniversalTensorSquare.sg24657`, `OAI.UniversalTensorSquare.sg24658`, `OAI.UniversalTensorSquare.sg24659`, `OAI.UniversalTensorSquare.sg24660`, `OAI.UniversalTensorSquare.sg24662`, `OAI.UniversalTensorSquare.sg24663`, `OAI.UniversalTensorSquare.sg24664`, `OAI.UniversalTensorSquare.sg24665`, `OAI.UniversalTensorSquare.sg24666`, `OAI.UniversalTensorSquare.sg24668`, `OAI.UniversalTensorSquare.sg24669`, `OAI.UniversalTensorSquare.sg24670`, `OAI.UniversalTensorSquare.sg24671`, `OAI.UniversalTensorSquare.sg24672`, `OAI.UniversalTensorSquare.sg24674`, `OAI.UniversalTensorSquare.sg24676`, `OAI.UniversalTensorSquare.sg24680`, `OAI.UniversalTensorSquare.sg24681`, `OAI.UniversalTensorSquare.sg24682`, `OAI.UniversalTensorSquare.sg24684`, `OAI.UniversalTensorSquare.sg24685`, `OAI.UniversalTensorSquare.sg24686`, `OAI.UniversalTensorSquare.sg24688`, `OAI.UniversalTensorSquare.sg24691`, `OAI.UniversalTensorSquare.sg24692`, `OAI.UniversalTensorSquare.sg24693`, `OAI.UniversalTensorSquare.sg24695`, `OAI.UniversalTensorSquare.sg24697`, `OAI.UniversalTensorSquare.sg24700`, `OAI.UniversalTensorSquare.sg24701`, `OAI.UniversalTensorSquare.sg24706`, `OAI.UniversalTensorSquare.sg24708`, `OAI.UniversalTensorSquare.sg24709`, `OAI.UniversalTensorSquare.sg24712`, `OAI.UniversalTensorSquare.sg24715`, `OAI.UniversalTensorSquare.sg24716`, `OAI.UniversalTensorSquare.sg24719`, `OAI.UniversalTensorSquare.sg24720`, `OAI.UniversalTensorSquare.sg24730`, `OAI.UniversalTensorSquare.sg24731`, `OAI.UniversalTensorSquare.sg24732`, `OAI.UniversalTensorSquare.sg24733`, `OAI.UniversalTensorSquare.sg24734`, `OAI.UniversalTensorSquare.sg24735`, `OAI.UniversalTensorSquare.sg24738`, `OAI.UniversalTensorSquare.sg24739`, `OAI.UniversalTensorSquare.sg24743`, `OAI.UniversalTensorSquare.sg24744`, `OAI.UniversalTensorSquare.sg24745`, `OAI.UniversalTensorSquare.sg24747`, `OAI.UniversalTensorSquare.sg24748`, `OAI.UniversalTensorSquare.sg24775`, `OAI.UniversalTensorSquare.sg24783`, `OAI.UniversalTensorSquare.sg24789`, `OAI.UniversalTensorSquare.sg24809`, `OAI.UniversalTensorSquare.sg24811`, `OAI.UniversalTensorSquare.sg24816`, `OAI.UniversalTensorSquare.sg24817`, `OAI.UniversalTensorSquare.sg24818`, `OAI.UniversalTensorSquare.sg24820`, `OAI.UniversalTensorSquare.sg24821`, `OAI.UniversalTensorSquare.sg24825`, `OAI.UniversalTensorSquare.sg24826`, `OAI.UniversalTensorSquare.sg24827`, `OAI.UniversalTensorSquare.sg24832`, `OAI.UniversalTensorSquare.sg24840`, `OAI.UniversalTensorSquare.sg24843`, `OAI.UniversalTensorSquare.sg24845`, `OAI.UniversalTensorSquare.sg24846`, `OAI.UniversalTensorSquare.sg24851`, `OAI.UniversalTensorSquare.sg24861`, `OAI.UniversalTensorSquare.sg24876`, `OAI.UniversalTensorSquare.sg24879`, `OAI.UniversalTensorSquare.sg24882`, `OAI.UniversalTensorSquare.sg24885`, `OAI.UniversalTensorSquare.sg24886`, `OAI.UniversalTensorSquare.sg24887`, `OAI.UniversalTensorSquare.sg24889`, `OAI.UniversalTensorSquare.sg24893`, `OAI.UniversalTensorSquare.sg24896`, `OAI.UniversalTensorSquare.sg24897`, `OAI.UniversalTensorSquare.sg24898`, `OAI.UniversalTensorSquare.sg24911`, `OAI.UniversalTensorSquare.sg24913`, `OAI.UniversalTensorSquare.sg24917`, `OAI.UniversalTensorSquare.sg24919`, `OAI.UniversalTensorSquare.sg24920`, `OAI.UniversalTensorSquare.sg24923`, `OAI.UniversalTensorSquare.sg24931`, `OAI.UniversalTensorSquare.sg24939`, `OAI.UniversalTensorSquare.sg24941`, `OAI.UniversalTensorSquare.sg24942`, `OAI.UniversalTensorSquare.sg24943`, `OAI.UniversalTensorSquare.sg24944`, `OAI.UniversalTensorSquare.sg24949`, `OAI.UniversalTensorSquare.sg24952`, `OAI.UniversalTensorSquare.sg24953`, `OAI.UniversalTensorSquare.sg24954`, `OAI.UniversalTensorSquare.sg24955`, `OAI.UniversalTensorSquare.sg24956`, `OAI.UniversalTensorSquare.sg24958`, `OAI.UniversalTensorSquare.sg24959`, `OAI.UniversalTensorSquare.sg24960`, `OAI.UniversalTensorSquare.sg24964`, `OAI.UniversalTensorSquare.sg24967`, `OAI.UniversalTensorSquare.sg24971`, `OAI.UniversalTensorSquare.sg24972`, `OAI.UniversalTensorSquare.sg24984`, `OAI.UniversalTensorSquare.sg24987`, `OAI.UniversalTensorSquare.sg24989`, `OAI.UniversalTensorSquare.sg24990`, `OAI.UniversalTensorSquare.sg24991`, `OAI.UniversalTensorSquare.sg24996`, `OAI.UniversalTensorSquare.sg24998`, `OAI.UniversalTensorSquare.sg25003`, `OAI.UniversalTensorSquare.sg25005`, `OAI.UniversalTensorSquare.sg25007`, `OAI.UniversalTensorSquare.sg25008`, `OAI.UniversalTensorSquare.sg25009`, `OAI.UniversalTensorSquare.sg25011`, `OAI.UniversalTensorSquare.sg25013`, `OAI.UniversalTensorSquare.sg25018`, `OAI.UniversalTensorSquare.sg25019`, `OAI.UniversalTensorSquare.sg25020`, `OAI.UniversalTensorSquare.sg25021`, `OAI.UniversalTensorSquare.sg25022`, `OAI.UniversalTensorSquare.sg25024`, `OAI.UniversalTensorSquare.sg25025`, `OAI.UniversalTensorSquare.sg25026`, `OAI.UniversalTensorSquare.sg25028`, `OAI.UniversalTensorSquare.sg25030`, `OAI.UniversalTensorSquare.sg25032`, `OAI.UniversalTensorSquare.sg25034`, `OAI.UniversalTensorSquare.sg25036`, `OAI.UniversalTensorSquare.sg25039`, `OAI.UniversalTensorSquare.sg25040`, `OAI.UniversalTensorSquare.sg25041`, `OAI.UniversalTensorSquare.sg25042`, `OAI.UniversalTensorSquare.sg25044`, `OAI.UniversalTensorSquare.sg25045`, `OAI.UniversalTensorSquare.sg25046`, `OAI.UniversalTensorSquare.sg25050`, `OAI.UniversalTensorSquare.sg25051`, `OAI.UniversalTensorSquare.sg25053`, `OAI.UniversalTensorSquare.sg25056`, `OAI.UniversalTensorSquare.sg25057`, `OAI.UniversalTensorSquare.sg25058`, `OAI.UniversalTensorSquare.sg25062`, `OAI.UniversalTensorSquare.sg25064`, `OAI.UniversalTensorSquare.sg25066`, `OAI.UniversalTensorSquare.sg25068`, `OAI.UniversalTensorSquare.sg25069`, `OAI.UniversalTensorSquare.sg25070`, `OAI.UniversalTensorSquare.sg25074`, `OAI.UniversalTensorSquare.sg25075`, `OAI.UniversalTensorSquare.sg25076`, `OAI.UniversalTensorSquare.sg25111`, `OAI.UniversalTensorSquare.sg25135`, `OAI.UniversalTensorSquare.sg25138`, `OAI.UniversalTensorSquare.sg25148`, `OAI.UniversalTensorSquare.sg25154`, `OAI.UniversalTensorSquare.sg25163`, `OAI.UniversalTensorSquare.sg25168`, `OAI.UniversalTensorSquare.sg25175`, `OAI.UniversalTensorSquare.sg25177`, `OAI.UniversalTensorSquare.sg25182`, `OAI.UniversalTensorSquare.sg25184`, `OAI.UniversalTensorSquare.sg25187`, `OAI.UniversalTensorSquare.sg25189`, `OAI.UniversalTensorSquare.sg25194`, `OAI.UniversalTensorSquare.sg25196`, `OAI.UniversalTensorSquare.sg25200`, `OAI.UniversalTensorSquare.sg25207`, `OAI.UniversalTensorSquare.sg25209`, `OAI.UniversalTensorSquare.sg25215`, `OAI.UniversalTensorSquare.sg25217`, `OAI.UniversalTensorSquare.sg25223`, `OAI.UniversalTensorSquare.sg25227`, `OAI.UniversalTensorSquare.sg25230`, `OAI.UniversalTensorSquare.sg25238`, `OAI.UniversalTensorSquare.sg25239`, `OAI.UniversalTensorSquare.sg25247`, `OAI.UniversalTensorSquare.sg25249`, `OAI.UniversalTensorSquare.sg25262`, `OAI.UniversalTensorSquare.sg25264`, `OAI.UniversalTensorSquare.sg25267`, `OAI.UniversalTensorSquare.sg25270`, `OAI.UniversalTensorSquare.sg25271`, `OAI.UniversalTensorSquare.sg25275`, `OAI.UniversalTensorSquare.sg25277`, `OAI.UniversalTensorSquare.sg25278`, `OAI.UniversalTensorSquare.sg25284`, `OAI.UniversalTensorSquare.sg25285`, `OAI.UniversalTensorSquare.sg25286`, `OAI.UniversalTensorSquare.sg25290`, `OAI.UniversalTensorSquare.sg25292`, `OAI.UniversalTensorSquare.sg25293`, `OAI.UniversalTensorSquare.sg25294`, `OAI.UniversalTensorSquare.sg25298`, `OAI.UniversalTensorSquare.sg25303`, `OAI.UniversalTensorSquare.sg25307`, `OAI.UniversalTensorSquare.sg25310`, `OAI.UniversalTensorSquare.sg25316`, `OAI.UniversalTensorSquare.sg25317`, `OAI.UniversalTensorSquare.sg25318`, `OAI.UniversalTensorSquare.sg25323`, `OAI.UniversalTensorSquare.sg25324`, `OAI.UniversalTensorSquare.sg25329`, `OAI.UniversalTensorSquare.sg25330`, `OAI.UniversalTensorSquare.sg25331`, `OAI.UniversalTensorSquare.sg25332`, `OAI.UniversalTensorSquare.sg25335`, `OAI.UniversalTensorSquare.sg25339`, `OAI.UniversalTensorSquare.sg25340`, `OAI.UniversalTensorSquare.sg25342`, `OAI.UniversalTensorSquare.sg25345`, `OAI.UniversalTensorSquare.sg25347`, `OAI.UniversalTensorSquare.sg25348`, `OAI.UniversalTensorSquare.sg25350`, `OAI.UniversalTensorSquare.sg25351`, `OAI.UniversalTensorSquare.sg25352`, `OAI.UniversalTensorSquare.sg25354`, `OAI.UniversalTensorSquare.sg25357`, `OAI.UniversalTensorSquare.sg25359`, `OAI.UniversalTensorSquare.sg25361`, `OAI.UniversalTensorSquare.sg25375`, `OAI.UniversalTensorSquare.sg25405`, `OAI.UniversalTensorSquare.sg25413`, `OAI.UniversalTensorSquare.sg25416`, `OAI.UniversalTensorSquare.sg25417`, `OAI.UniversalTensorSquare.sg25448`, `OAI.UniversalTensorSquare.sg25456`, `OAI.UniversalTensorSquare.sg25457`, `OAI.UniversalTensorSquare.sg25472`, `OAI.UniversalTensorSquare.sg25476`, `OAI.UniversalTensorSquare.sg25478`, `OAI.UniversalTensorSquare.sg25486`, `OAI.UniversalTensorSquare.sg25487`, `OAI.UniversalTensorSquare.sg25498`, `OAI.UniversalTensorSquare.sg25503`, `OAI.UniversalTensorSquare.sg25506`, `OAI.UniversalTensorSquare.sg25508`, `OAI.UniversalTensorSquare.sg25518`, `OAI.UniversalTensorSquare.sg25522`, `OAI.UniversalTensorSquare.sg25557`, `OAI.UniversalTensorSquare.sg25560`, `OAI.UniversalTensorSquare.sg25569`, `OAI.UniversalTensorSquare.sg25572`, `OAI.UniversalTensorSquare.sg25574`, `OAI.UniversalTensorSquare.sg25587`, `OAI.UniversalTensorSquare.sg25589`, `OAI.UniversalTensorSquare.sg25603`, `OAI.UniversalTensorSquare.sg25605`, `OAI.UniversalTensorSquare.sg25607`, `OAI.UniversalTensorSquare.sg25614`, `OAI.UniversalTensorSquare.sg25630`, `OAI.UniversalTensorSquare.sg25638`, `OAI.UniversalTensorSquare.sg25643`, `OAI.UniversalTensorSquare.sg25645`, `OAI.UniversalTensorSquare.sg25646`, `OAI.UniversalTensorSquare.sg25653`, `OAI.UniversalTensorSquare.sg25654`, `OAI.UniversalTensorSquare.sg25664`, `OAI.UniversalTensorSquare.sg25674`, `OAI.UniversalTensorSquare.sg25675`, `OAI.UniversalTensorSquare.sg25682`, `OAI.UniversalTensorSquare.sg25691`, `OAI.UniversalTensorSquare.sg25694`, `OAI.UniversalTensorSquare.sg25697`, `OAI.UniversalTensorSquare.sg25706`, `OAI.UniversalTensorSquare.sg25707`, `OAI.UniversalTensorSquare.sg25711`, `OAI.UniversalTensorSquare.sg25714`, `OAI.UniversalTensorSquare.sg25715`, `OAI.UniversalTensorSquare.sg25716`, `OAI.UniversalTensorSquare.sg25722`, `OAI.UniversalTensorSquare.sg25723`, `OAI.UniversalTensorSquare.sg25728`, `OAI.UniversalTensorSquare.sg25729`, `OAI.UniversalTensorSquare.sg25730`, `OAI.UniversalTensorSquare.sg25733`, `OAI.UniversalTensorSquare.sg25735`, `OAI.UniversalTensorSquare.sg25736`, `OAI.UniversalTensorSquare.sg25741`, `OAI.UniversalTensorSquare.sg25743`, `OAI.UniversalTensorSquare.sg25760`, `OAI.UniversalTensorSquare.sg25764`, `OAI.UniversalTensorSquare.sg25771`, `OAI.UniversalTensorSquare.sg25777`, `OAI.UniversalTensorSquare.sg25782`, `OAI.UniversalTensorSquare.sg25793`, `OAI.UniversalTensorSquare.sg25797`, `OAI.UniversalTensorSquare.sg25800`, `OAI.UniversalTensorSquare.sg25803`, `OAI.UniversalTensorSquare.sg25805`, `OAI.UniversalTensorSquare.sg25813`, `OAI.UniversalTensorSquare.sg25817`, `OAI.UniversalTensorSquare.sg25820`, `OAI.UniversalTensorSquare.sg25821`, `OAI.UniversalTensorSquare.sg25824`, `OAI.UniversalTensorSquare.sg25826`, `OAI.UniversalTensorSquare.sg25829`, `OAI.UniversalTensorSquare.sg25835`, `OAI.UniversalTensorSquare.sg25839`, `OAI.UniversalTensorSquare.sg25842`, `OAI.UniversalTensorSquare.sg25848`, `OAI.UniversalTensorSquare.sg25850`, `OAI.UniversalTensorSquare.sg25852`, `OAI.UniversalTensorSquare.sg25855`, `OAI.UniversalTensorSquare.sg25856`, `OAI.UniversalTensorSquare.sg25857`, `OAI.UniversalTensorSquare.sg25858`, `OAI.UniversalTensorSquare.sg25859`, `OAI.UniversalTensorSquare.sg25864`, `OAI.UniversalTensorSquare.sg25871`, `OAI.UniversalTensorSquare.sg25872`, `OAI.UniversalTensorSquare.sg25874`, `OAI.UniversalTensorSquare.sg25875`, `OAI.UniversalTensorSquare.sg25880`, `OAI.UniversalTensorSquare.sg25882`, `OAI.UniversalTensorSquare.sg25885`, `OAI.UniversalTensorSquare.sg25891`, `OAI.UniversalTensorSquare.sg25892`, `OAI.UniversalTensorSquare.sg25896`, `OAI.UniversalTensorSquare.sg25898`, `OAI.UniversalTensorSquare.sg25900`, `OAI.UniversalTensorSquare.sg25902`, `OAI.UniversalTensorSquare.sg25940`, `OAI.UniversalTensorSquare.sg25941`, `OAI.UniversalTensorSquare.sg25945`, `OAI.UniversalTensorSquare.sg25961`, `OAI.UniversalTensorSquare.sg25966`, `OAI.UniversalTensorSquare.sg25974`, `OAI.UniversalTensorSquare.sg25981`, `OAI.UniversalTensorSquare.sg25982`, `OAI.UniversalTensorSquare.sg25983`, `OAI.UniversalTensorSquare.sg25987`, `OAI.UniversalTensorSquare.sg26022`, `OAI.UniversalTensorSquare.sg26030`, `OAI.UniversalTensorSquare.sg26040`, `OAI.UniversalTensorSquare.sg26041`, `OAI.UniversalTensorSquare.sg26044`, `OAI.UniversalTensorSquare.sg26051`, `OAI.UniversalTensorSquare.sg26053`, `OAI.UniversalTensorSquare.sg26066`, `OAI.UniversalTensorSquare.sg26080`, `OAI.UniversalTensorSquare.sg26084`, `OAI.UniversalTensorSquare.sg26086`, `OAI.UniversalTensorSquare.sg26094`, `OAI.UniversalTensorSquare.sg26110`, `OAI.UniversalTensorSquare.sg26112`, `OAI.UniversalTensorSquare.sg26116`, `OAI.UniversalTensorSquare.sg26122`, `OAI.UniversalTensorSquare.sg26124`, `OAI.UniversalTensorSquare.sg26129`, `OAI.UniversalTensorSquare.sg26136`, `OAI.UniversalTensorSquare.sg26138`, `OAI.UniversalTensorSquare.sg26140`, `OAI.UniversalTensorSquare.sg26141`, `OAI.UniversalTensorSquare.sg26153`, `OAI.UniversalTensorSquare.sg26158`, `OAI.UniversalTensorSquare.sg26163`, `OAI.UniversalTensorSquare.sg26165`, `OAI.UniversalTensorSquare.sg26169`, `OAI.UniversalTensorSquare.sg26175`, `OAI.UniversalTensorSquare.sg26177`, `OAI.UniversalTensorSquare.sg26182`, `OAI.UniversalTensorSquare.sg26184`, `OAI.UniversalTensorSquare.sg26186`, `OAI.UniversalTensorSquare.sg26187`, `OAI.UniversalTensorSquare.sg26189`, `OAI.UniversalTensorSquare.sg26194`, `OAI.UniversalTensorSquare.sg26196`, `OAI.UniversalTensorSquare.sg26197`, `OAI.UniversalTensorSquare.sg26199`, `OAI.UniversalTensorSquare.sg26204`, `OAI.UniversalTensorSquare.sg26205`, `OAI.UniversalTensorSquare.sg26206`, `OAI.UniversalTensorSquare.sg26207`, `OAI.UniversalTensorSquare.sg26210`, `OAI.UniversalTensorSquare.sg26211`, `OAI.UniversalTensorSquare.sg26215`, `OAI.UniversalTensorSquare.sg26217`, `OAI.UniversalTensorSquare.sg26229`, `OAI.UniversalTensorSquare.sg26234`, `OAI.UniversalTensorSquare.sg26240`, `OAI.UniversalTensorSquare.sg26249`, `OAI.UniversalTensorSquare.sg26252`, `OAI.UniversalTensorSquare.sg26260`, `OAI.UniversalTensorSquare.sg26265`, `OAI.UniversalTensorSquare.sg26266`, `OAI.UniversalTensorSquare.sg26270`, `OAI.UniversalTensorSquare.sg26271`, `OAI.UniversalTensorSquare.sg26273`, `OAI.UniversalTensorSquare.sg26276`, `OAI.UniversalTensorSquare.sg26282`, `OAI.UniversalTensorSquare.sg26284`, `OAI.UniversalTensorSquare.sg26286`, `OAI.UniversalTensorSquare.sg26289`, `OAI.UniversalTensorSquare.sg26291`, `OAI.UniversalTensorSquare.sg26292`, `OAI.UniversalTensorSquare.sg26293`, `OAI.UniversalTensorSquare.sg26320`, `OAI.UniversalTensorSquare.sg26322`, `OAI.UniversalTensorSquare.sg26323`, `OAI.UniversalTensorSquare.sg26324`, `OAI.UniversalTensorSquare.sg26326`, `OAI.UniversalTensorSquare.sg26328`, `OAI.UniversalTensorSquare.sg26329`, `OAI.UniversalTensorSquare.sg26332`, `OAI.UniversalTensorSquare.sg26345`, `OAI.UniversalTensorSquare.sg26347`, `OAI.UniversalTensorSquare.sg26350`, `OAI.UniversalTensorSquare.sg26351`, `OAI.UniversalTensorSquare.sg26355`, `OAI.UniversalTensorSquare.sg26359`, `OAI.UniversalTensorSquare.sg26363`, `OAI.UniversalTensorSquare.sg26374`, `OAI.UniversalTensorSquare.sg26380`, `OAI.UniversalTensorSquare.sg26389`, `OAI.UniversalTensorSquare.sg26397`, `OAI.UniversalTensorSquare.sg26398`, `OAI.UniversalTensorSquare.sg26409`, `OAI.UniversalTensorSquare.sg26412`, `OAI.UniversalTensorSquare.sg26415`, `OAI.UniversalTensorSquare.sg26416`, `OAI.UniversalTensorSquare.sg26423`, `OAI.UniversalTensorSquare.sg26430`, `OAI.UniversalTensorSquare.sg26433`, `OAI.UniversalTensorSquare.sg26443`, `OAI.UniversalTensorSquare.sg26444`, `OAI.UniversalTensorSquare.sg26445`, `OAI.UniversalTensorSquare.sg26450`, `OAI.UniversalTensorSquare.sg26466`, `OAI.UniversalTensorSquare.sg26467`, `OAI.UniversalTensorSquare.sg26477`, `OAI.UniversalTensorSquare.sg26484`, `OAI.UniversalTensorSquare.sg26485`, `OAI.UniversalTensorSquare.sg26486`, `OAI.UniversalTensorSquare.sg26490`, `OAI.UniversalTensorSquare.sg26491`, `OAI.UniversalTensorSquare.sg26494`, `OAI.UniversalTensorSquare.sg26496`, `OAI.UniversalTensorSquare.sg26500`, `OAI.UniversalTensorSquare.sg26502`, `OAI.UniversalTensorSquare.sg26504`, `OAI.UniversalTensorSquare.sg26506`, `OAI.UniversalTensorSquare.sg26511`, `OAI.UniversalTensorSquare.sg26513`, `OAI.UniversalTensorSquare.sg26514`, `OAI.UniversalTensorSquare.sg26517`, `OAI.UniversalTensorSquare.sg26520`, `OAI.UniversalTensorSquare.sg26521`, `OAI.UniversalTensorSquare.sg26522`, `OAI.UniversalTensorSquare.sg26529`, `OAI.UniversalTensorSquare.sg26531`, `OAI.UniversalTensorSquare.sg26533`, `OAI.UniversalTensorSquare.sg26541`, `OAI.UniversalTensorSquare.sg26543`, `OAI.UniversalTensorSquare.sg26544`, `OAI.UniversalTensorSquare.sg26570`, `OAI.UniversalTensorSquare.sg26576`, `OAI.UniversalTensorSquare.sg26592`, `OAI.UniversalTensorSquare.sg26594`, `OAI.UniversalTensorSquare.sg26598`, `OAI.UniversalTensorSquare.sg26599`, `OAI.UniversalTensorSquare.sg26604`, `OAI.UniversalTensorSquare.sg26613`, `OAI.UniversalTensorSquare.sg26614`, `OAI.UniversalTensorSquare.sg26616`, `OAI.UniversalTensorSquare.sg26617`, `OAI.UniversalTensorSquare.sg26628`, `OAI.UniversalTensorSquare.sg26633`, `OAI.UniversalTensorSquare.sg26634`, `OAI.UniversalTensorSquare.sg26644`, `OAI.UniversalTensorSquare.sg26645`, `OAI.UniversalTensorSquare.sg26650`, `OAI.UniversalTensorSquare.sg26651`, `OAI.UniversalTensorSquare.sg26662`, `OAI.UniversalTensorSquare.sg26666`, `OAI.UniversalTensorSquare.sg26671`, `OAI.UniversalTensorSquare.sg26674`, `OAI.UniversalTensorSquare.sg26686`, `OAI.UniversalTensorSquare.sg26689`, `OAI.UniversalTensorSquare.sg26697`, `OAI.UniversalTensorSquare.sg26698`, `OAI.UniversalTensorSquare.sg26702`, `OAI.UniversalTensorSquare.sg26707`, `OAI.UniversalTensorSquare.sg26712`, `OAI.UniversalTensorSquare.sg26715`, `OAI.UniversalTensorSquare.sg26724`, `OAI.UniversalTensorSquare.sg26726`, `OAI.UniversalTensorSquare.sg26731`, `OAI.UniversalTensorSquare.sg26738`, `OAI.UniversalTensorSquare.sg26742`, `OAI.UniversalTensorSquare.sg26745`, `OAI.UniversalTensorSquare.sg26746`, `OAI.UniversalTensorSquare.sg26747`, `OAI.UniversalTensorSquare.sg26752`, `OAI.UniversalTensorSquare.sg26757`, `OAI.UniversalTensorSquare.sg26758`, `OAI.UniversalTensorSquare.sg26759`, `OAI.UniversalTensorSquare.sg26763`, `OAI.UniversalTensorSquare.sg26764`, `OAI.UniversalTensorSquare.sg26765`, `OAI.UniversalTensorSquare.sg26769`, `OAI.UniversalTensorSquare.sg26811`, `OAI.UniversalTensorSquare.sg26823`, `OAI.UniversalTensorSquare.sg26824`, `OAI.UniversalTensorSquare.sg26849`, `OAI.UniversalTensorSquare.sg26859`, `OAI.UniversalTensorSquare.sg26860`, `OAI.UniversalTensorSquare.sg26865`, `OAI.UniversalTensorSquare.sg26873`, `OAI.UniversalTensorSquare.sg26877`, `OAI.UniversalTensorSquare.sg26881`, `OAI.UniversalTensorSquare.sg26884`, `OAI.UniversalTensorSquare.sg26892`, `OAI.UniversalTensorSquare.sg26898`, `OAI.UniversalTensorSquare.sg26899`, `OAI.UniversalTensorSquare.sg26900`, `OAI.UniversalTensorSquare.sg26927`, `OAI.UniversalTensorSquare.sg26930`, `OAI.UniversalTensorSquare.sg26942`, `OAI.UniversalTensorSquare.sg26944`, `OAI.UniversalTensorSquare.sg26946`, `OAI.UniversalTensorSquare.sg26947`, `OAI.UniversalTensorSquare.sg26949`, `OAI.UniversalTensorSquare.sg26950`, `OAI.UniversalTensorSquare.sg26954`, `OAI.UniversalTensorSquare.sg26955`, `OAI.UniversalTensorSquare.sg26956`, `OAI.UniversalTensorSquare.sg26957`, `OAI.UniversalTensorSquare.sg26958`, `OAI.UniversalTensorSquare.sg26959`, `OAI.UniversalTensorSquare.sg26960`, `OAI.UniversalTensorSquare.sg26963`, `OAI.UniversalTensorSquare.sg26972`, `OAI.UniversalTensorSquare.sg27002`, `OAI.UniversalTensorSquare.sg27004`, `OAI.UniversalTensorSquare.sg27005`, `OAI.UniversalTensorSquare.sg27007`, `OAI.UniversalTensorSquare.sg27009`, `OAI.UniversalTensorSquare.sg27011`, `OAI.UniversalTensorSquare.sg27013`, `OAI.UniversalTensorSquare.sg27014`, `OAI.UniversalTensorSquare.sg27015`, `OAI.UniversalTensorSquare.sg27019`, `OAI.UniversalTensorSquare.sg27059`, `OAI.UniversalTensorSquare.sg27063`, `OAI.UniversalTensorSquare.sg27066`, `OAI.UniversalTensorSquare.sg27072`, `OAI.UniversalTensorSquare.sg27074`, `OAI.UniversalTensorSquare.sg27075`, `OAI.UniversalTensorSquare.sg27078`, `OAI.UniversalTensorSquare.sg27079`, `OAI.UniversalTensorSquare.sg27083`, `OAI.UniversalTensorSquare.sg27085`, `OAI.UniversalTensorSquare.sg27087`, `OAI.UniversalTensorSquare.sg27089`, `OAI.UniversalTensorSquare.sg27091`, `OAI.UniversalTensorSquare.sg27092`, `OAI.UniversalTensorSquare.sg27093`, `OAI.UniversalTensorSquare.sg27095`, `OAI.UniversalTensorSquare.sg27096`, `OAI.UniversalTensorSquare.sg27097`, `OAI.UniversalTensorSquare.sg27107`, `OAI.UniversalTensorSquare.sg27108`, `OAI.UniversalTensorSquare.sg27109`, `OAI.UniversalTensorSquare.sg27111`, `OAI.UniversalTensorSquare.sg27112`, `OAI.UniversalTensorSquare.sg27115`, `OAI.UniversalTensorSquare.sg27119`, `OAI.UniversalTensorSquare.sg27121`, `OAI.UniversalTensorSquare.sg27122`, `OAI.UniversalTensorSquare.sg27124`, `OAI.UniversalTensorSquare.sg27125`, `OAI.UniversalTensorSquare.sg27127`, `OAI.UniversalTensorSquare.sg27129`, `OAI.UniversalTensorSquare.sg27130`, `OAI.UniversalTensorSquare.sg27131`, `OAI.UniversalTensorSquare.sg27161`, `OAI.UniversalTensorSquare.sg27165`, `OAI.UniversalTensorSquare.sg27175`, `OAI.UniversalTensorSquare.sg27186`, `OAI.UniversalTensorSquare.sg27188`, `OAI.UniversalTensorSquare.sg27190`, `OAI.UniversalTensorSquare.sg27197`, `OAI.UniversalTensorSquare.sg27198`, `OAI.UniversalTensorSquare.sg27200`, `OAI.UniversalTensorSquare.sg27202`, `OAI.UniversalTensorSquare.sg27206`, `OAI.UniversalTensorSquare.sg27209`, `OAI.UniversalTensorSquare.sg27213`, `OAI.UniversalTensorSquare.sg27217`, `OAI.UniversalTensorSquare.sg27219`, `OAI.UniversalTensorSquare.sg27222`, `OAI.UniversalTensorSquare.sg27227`, `OAI.UniversalTensorSquare.sg27228`, `OAI.UniversalTensorSquare.sg27231`, `OAI.UniversalTensorSquare.sg27233`, `OAI.UniversalTensorSquare.sg27236`, `OAI.UniversalTensorSquare.sg27237`, `OAI.UniversalTensorSquare.sg27247`, `OAI.UniversalTensorSquare.sg27249`, `OAI.UniversalTensorSquare.sg27251`, `OAI.UniversalTensorSquare.sg27253`, `OAI.UniversalTensorSquare.sg27254`, `OAI.UniversalTensorSquare.sg27255`, `OAI.UniversalTensorSquare.sg27258`, `OAI.UniversalTensorSquare.sg27259`, `OAI.UniversalTensorSquare.sg27260`, `OAI.UniversalTensorSquare.sg27262`, `OAI.UniversalTensorSquare.sg27263`, `OAI.UniversalTensorSquare.sg27264`, `OAI.UniversalTensorSquare.sg27265`, `OAI.UniversalTensorSquare.sg27266`, `OAI.UniversalTensorSquare.sg27267`, `OAI.UniversalTensorSquare.sg27268`, `OAI.UniversalTensorSquare.sg27269`, `OAI.UniversalTensorSquare.sg27272`, `OAI.UniversalTensorSquare.sg27275`, `OAI.UniversalTensorSquare.sg27277`, `OAI.UniversalTensorSquare.sg27279`, `OAI.UniversalTensorSquare.sg27280`, `OAI.UniversalTensorSquare.sg27281`, `OAI.UniversalTensorSquare.sg27282`, `OAI.UniversalTensorSquare.sg27283`, `OAI.UniversalTensorSquare.sg27288`, `OAI.UniversalTensorSquare.sg27289`, `OAI.UniversalTensorSquare.sg27292`, `OAI.UniversalTensorSquare.sg27300`, `OAI.UniversalTensorSquare.sg27302`, `OAI.UniversalTensorSquare.sg27303`, `OAI.UniversalTensorSquare.sg27308`, `OAI.UniversalTensorSquare.sg27310`, `OAI.UniversalTensorSquare.sg27312`, `OAI.UniversalTensorSquare.sg27313`, `OAI.UniversalTensorSquare.sg27321`, `OAI.UniversalTensorSquare.sg27323`, `OAI.UniversalTensorSquare.sg27324`, `OAI.UniversalTensorSquare.sg27329`, `OAI.UniversalTensorSquare.sg27333`, `OAI.UniversalTensorSquare.sg27336`, `OAI.UniversalTensorSquare.sg27338`, `OAI.UniversalTensorSquare.sg27342`, `OAI.UniversalTensorSquare.sg27345`, `OAI.UniversalTensorSquare.sg27347`, `OAI.UniversalTensorSquare.sg27349`, `OAI.UniversalTensorSquare.sg27352`, `OAI.UniversalTensorSquare.sg27358`, `OAI.UniversalTensorSquare.sg27364`, `OAI.UniversalTensorSquare.sg27365`, `OAI.UniversalTensorSquare.sg27368`, `OAI.UniversalTensorSquare.sg27370`, `OAI.UniversalTensorSquare.sg27373`, `OAI.UniversalTensorSquare.sg27379`, `OAI.UniversalTensorSquare.sg27382`, `OAI.UniversalTensorSquare.sg27383`, `OAI.UniversalTensorSquare.sg27384`, `OAI.UniversalTensorSquare.sg27387`, `OAI.UniversalTensorSquare.sg27391`, `OAI.UniversalTensorSquare.sg27394`, `OAI.UniversalTensorSquare.sg27400`, `OAI.UniversalTensorSquare.sg27408`, `OAI.UniversalTensorSquare.sg27409`, `OAI.UniversalTensorSquare.sg27410`, `OAI.UniversalTensorSquare.sg27412`, `OAI.UniversalTensorSquare.sg27414`, `OAI.UniversalTensorSquare.sg27415`, `OAI.UniversalTensorSquare.sg27420`, `OAI.UniversalTensorSquare.sg27422`, `OAI.UniversalTensorSquare.sg27426`, `OAI.UniversalTensorSquare.sg27430`, `OAI.UniversalTensorSquare.sg27437`, `OAI.UniversalTensorSquare.sg27438`, `OAI.UniversalTensorSquare.sg27443`, `OAI.UniversalTensorSquare.sg27448`, `OAI.UniversalTensorSquare.sg27452`, `OAI.UniversalTensorSquare.sg27453`, `OAI.UniversalTensorSquare.sg27458`, `OAI.UniversalTensorSquare.sg27462`, `OAI.UniversalTensorSquare.sg27463`, `OAI.UniversalTensorSquare.sg27464`, `OAI.UniversalTensorSquare.sg27465`, `OAI.UniversalTensorSquare.sg27466`, `OAI.UniversalTensorSquare.sg27468`, `OAI.UniversalTensorSquare.sg27469`, `OAI.UniversalTensorSquare.sg27471`, `OAI.UniversalTensorSquare.sg27473`, `OAI.UniversalTensorSquare.sg27475`, `OAI.UniversalTensorSquare.sg27476`, `OAI.UniversalTensorSquare.sg27477`, `OAI.UniversalTensorSquare.sg27479`, `OAI.UniversalTensorSquare.sg27484`, `OAI.UniversalTensorSquare.sg27485`, `OAI.UniversalTensorSquare.sg27486`, `OAI.UniversalTensorSquare.sg27488`, `OAI.UniversalTensorSquare.sg27490`, `OAI.UniversalTensorSquare.sg27491`, `OAI.UniversalTensorSquare.sg27493`, `OAI.UniversalTensorSquare.sg27498`, `OAI.UniversalTensorSquare.sg27500`, `OAI.UniversalTensorSquare.sg27501`, `OAI.UniversalTensorSquare.sg27503`, `OAI.UniversalTensorSquare.sg27524`, `OAI.UniversalTensorSquare.sg27530`, `OAI.UniversalTensorSquare.sg27535`, `OAI.UniversalTensorSquare.sg27539`, `OAI.UniversalTensorSquare.sg27541`, `OAI.UniversalTensorSquare.sg27543`, `OAI.UniversalTensorSquare.sg27575`, `OAI.UniversalTensorSquare.sg27578`, `OAI.UniversalTensorSquare.sg27581`, `OAI.UniversalTensorSquare.sg27708`, `OAI.UniversalTensorSquare.sg27856`, `OAI.UniversalTensorSquare.sg27859`, `OAI.UniversalTensorSquare.sg27955`, `OAI.UniversalTensorSquare.sg27956`, `OAI.UniversalTensorSquare.sg27958`, `OAI.UniversalTensorSquare.sg28004`, `OAI.UniversalTensorSquare.sg28005`, `OAI.UniversalTensorSquare.sg28007`, `OAI.UniversalTensorSquare.sg28041`, `OAI.UniversalTensorSquare.sg28042`, `OAI.UniversalTensorSquare.sg28044`, `OAI.UniversalTensorSquare.sg28068`, `OAI.UniversalTensorSquare.sg28083`, `OAI.UniversalTensorSquare.sg28095`, `OAI.UniversalTensorSquare.sg28113`, `OAI.UniversalTensorSquare.sg28128`, `OAI.UniversalTensorSquare.sg28237`, `OAI.UniversalTensorSquare.sg28246`, `OAI.UniversalTensorSquare.sg28248`, `OAI.UniversalTensorSquare.sg28276`, `OAI.UniversalTensorSquare.sg28283`, `OAI.UniversalTensorSquare.sg28306`, `OAI.UniversalTensorSquare.sg28309`, `OAI.UniversalTensorSquare.sg28326`, `OAI.UniversalTensorSquare.sg28360`, `OAI.UniversalTensorSquare.sg28368`, `OAI.UniversalTensorSquare.sg28370`, `OAI.UniversalTensorSquare.sg28372`, `OAI.UniversalTensorSquare.sg28374`, `OAI.UniversalTensorSquare.sg28380`, `OAI.UniversalTensorSquare.sg28381`, `OAI.UniversalTensorSquare.sg28383`, `OAI.UniversalTensorSquare.sg28388`, `OAI.UniversalTensorSquare.sg28397`, `OAI.UniversalTensorSquare.sg28450`, `OAI.UniversalTensorSquare.sg28458`, `OAI.UniversalTensorSquare.sg28459`, `OAI.UniversalTensorSquare.sg28494`, `OAI.UniversalTensorSquare.sg28495`, `OAI.UniversalTensorSquare.sg28496`, `OAI.UniversalTensorSquare.sg28505`, `OAI.UniversalTensorSquare.sg28506`, `OAI.UniversalTensorSquare.sg28539`, `OAI.UniversalTensorSquare.sg28540`, `OAI.UniversalTensorSquare.sg28546`, `OAI.UniversalTensorSquare.sg28563`, `OAI.UniversalTensorSquare.sg28564`, `OAI.UniversalTensorSquare.sg28572`, `OAI.UniversalTensorSquare.sg28575`, `OAI.UniversalTensorSquare.sg28584`, `OAI.UniversalTensorSquare.sg28605`, `OAI.UniversalTensorSquare.sg28622`, `OAI.UniversalTensorSquare.sg28643`, `OAI.UniversalTensorSquare.sg28654`, `OAI.UniversalTensorSquare.sg28659`, `OAI.UniversalTensorSquare.sg28662`, `OAI.UniversalTensorSquare.sg28667`, `OAI.UniversalTensorSquare.sg28688`, `OAI.UniversalTensorSquare.sg28695`, `OAI.UniversalTensorSquare.sg28697`, `OAI.UniversalTensorSquare.sg28714`, `OAI.UniversalTensorSquare.sg28741`, `OAI.UniversalTensorSquare.sg28753`, `OAI.UniversalTensorSquare.sg28759`, `OAI.UniversalTensorSquare.sg28761`, `OAI.UniversalTensorSquare.sg28766`, `OAI.UniversalTensorSquare.sg28768`, `OAI.UniversalTensorSquare.sg28769`, `OAI.UniversalTensorSquare.sg28775`, `OAI.UniversalTensorSquare.sg28780`, `OAI.UniversalTensorSquare.sg28788`, `OAI.UniversalTensorSquare.sg28791`, `OAI.UniversalTensorSquare.sg28792`, `OAI.UniversalTensorSquare.sg28796`, `OAI.UniversalTensorSquare.sg28808`, `OAI.UniversalTensorSquare.sg28819`, `OAI.UniversalTensorSquare.sg28822`, `OAI.UniversalTensorSquare.sg28826`, `OAI.UniversalTensorSquare.sg28827`, `OAI.UniversalTensorSquare.sg28833`, `OAI.UniversalTensorSquare.sg28841`, `OAI.UniversalTensorSquare.sg28847`, `OAI.UniversalTensorSquare.sg28848`, `OAI.UniversalTensorSquare.sg28849`, `OAI.UniversalTensorSquare.sg28850`, `OAI.UniversalTensorSquare.sg28851`, `OAI.UniversalTensorSquare.sg28853`, `OAI.UniversalTensorSquare.sg28894`, `OAI.UniversalTensorSquare.sg28898`, `OAI.UniversalTensorSquare.sg28920`, `OAI.UniversalTensorSquare.sg28943`, `OAI.UniversalTensorSquare.sg28954`, `OAI.UniversalTensorSquare.sg28987`, `OAI.UniversalTensorSquare.sg28988`, `OAI.UniversalTensorSquare.sg29001`, `OAI.UniversalTensorSquare.sg29008`, `OAI.UniversalTensorSquare.sg29014`, `OAI.UniversalTensorSquare.sg29036`, `OAI.UniversalTensorSquare.sg29037`, `OAI.UniversalTensorSquare.sg29038`, `OAI.UniversalTensorSquare.sg29056`, `OAI.UniversalTensorSquare.sg29057`, `OAI.UniversalTensorSquare.sg29088`, `OAI.UniversalTensorSquare.sg29090`, `OAI.UniversalTensorSquare.sg29098`, `OAI.UniversalTensorSquare.sg29104`, `OAI.UniversalTensorSquare.sg29106`, `OAI.UniversalTensorSquare.sg29115`, `OAI.UniversalTensorSquare.sg29125`, `OAI.UniversalTensorSquare.sg29128`, `OAI.UniversalTensorSquare.sg29130`, `OAI.UniversalTensorSquare.sg29132`, `OAI.UniversalTensorSquare.sg29137`, `OAI.UniversalTensorSquare.sg29164`, `OAI.UniversalTensorSquare.sg29166`, `OAI.UniversalTensorSquare.sg29175`, `OAI.UniversalTensorSquare.sg29176`, `OAI.UniversalTensorSquare.sg29183`, `OAI.UniversalTensorSquare.sg29184`, `OAI.UniversalTensorSquare.sg29191`, `OAI.UniversalTensorSquare.sg29192`, `OAI.UniversalTensorSquare.sg29194`, `OAI.UniversalTensorSquare.sg29219`, `OAI.UniversalTensorSquare.sg29220`, `OAI.UniversalTensorSquare.sg29238`, `OAI.UniversalTensorSquare.sg29239`, `OAI.UniversalTensorSquare.sg29243`, `OAI.UniversalTensorSquare.sg29259`, `OAI.UniversalTensorSquare.sg29260`, `OAI.UniversalTensorSquare.sg29270`, `OAI.UniversalTensorSquare.sg29271`, `OAI.UniversalTensorSquare.sg29272`, `OAI.UniversalTensorSquare.sg29274`, `OAI.UniversalTensorSquare.sg29278`, `OAI.UniversalTensorSquare.sg29282`, `OAI.UniversalTensorSquare.sg29284`, `OAI.UniversalTensorSquare.sg29287`, `OAI.UniversalTensorSquare.sg29291`, `OAI.UniversalTensorSquare.sg29292`, `OAI.UniversalTensorSquare.sg29297`, `OAI.UniversalTensorSquare.sg29303`, `OAI.UniversalTensorSquare.sg29324`, `OAI.UniversalTensorSquare.sg29325`, `OAI.UniversalTensorSquare.sg29330`, `OAI.UniversalTensorSquare.sg29331`, `OAI.UniversalTensorSquare.sg29332`, `OAI.UniversalTensorSquare.sg29363`, `OAI.UniversalTensorSquare.sg29364`, `OAI.UniversalTensorSquare.sg29366`, `OAI.UniversalTensorSquare.sg29370`, `OAI.UniversalTensorSquare.sg29390`, `OAI.UniversalTensorSquare.sg29391`, `OAI.UniversalTensorSquare.sg29392`, `OAI.UniversalTensorSquare.sg29393`, `OAI.UniversalTensorSquare.sg29399`, `OAI.UniversalTensorSquare.sg29404`, `OAI.UniversalTensorSquare.sg29409`, `OAI.UniversalTensorSquare.sg29415`, `OAI.UniversalTensorSquare.sg29420`, `OAI.UniversalTensorSquare.sg29421`, `OAI.UniversalTensorSquare.sg29424`, `OAI.UniversalTensorSquare.sg29432`, `OAI.UniversalTensorSquare.sg29433`, `OAI.UniversalTensorSquare.sg29435`, `OAI.UniversalTensorSquare.sg29444`, `OAI.UniversalTensorSquare.sg29446`, `OAI.UniversalTensorSquare.sg29447`, `OAI.UniversalTensorSquare.sg29448`, `OAI.UniversalTensorSquare.sg29452`, `OAI.UniversalTensorSquare.sg29453`, `OAI.UniversalTensorSquare.sg29454`, `OAI.UniversalTensorSquare.sg29456`, `OAI.UniversalTensorSquare.sg29457`, `OAI.UniversalTensorSquare.sg29465`, `OAI.UniversalTensorSquare.sg29477`, `OAI.UniversalTensorSquare.sg29478`, `OAI.UniversalTensorSquare.sg29481`, `OAI.UniversalTensorSquare.sg29489`, `OAI.UniversalTensorSquare.sg29495`, `OAI.UniversalTensorSquare.sg29496`, `OAI.UniversalTensorSquare.sg29503`, `OAI.UniversalTensorSquare.sg29505`, `OAI.UniversalTensorSquare.sg29507`, `OAI.UniversalTensorSquare.sg29508`, `OAI.UniversalTensorSquare.sg29509`, `OAI.UniversalTensorSquare.sg29510`, `OAI.UniversalTensorSquare.sg29519`, `OAI.UniversalTensorSquare.sg29520`, `OAI.UniversalTensorSquare.sg29521`, `OAI.UniversalTensorSquare.sg29522`, `OAI.UniversalTensorSquare.sg29524`, `OAI.UniversalTensorSquare.sg29525`, `OAI.UniversalTensorSquare.sg29528`, `OAI.UniversalTensorSquare.sg29529`, `OAI.UniversalTensorSquare.sg29555`, `OAI.UniversalTensorSquare.sg29556`, `OAI.UniversalTensorSquare.sg29557`, `OAI.UniversalTensorSquare.sg29558`, `OAI.UniversalTensorSquare.sg29560`, `OAI.UniversalTensorSquare.sg29563`, `OAI.UniversalTensorSquare.sg29564`, `OAI.UniversalTensorSquare.sg29568`, `OAI.UniversalTensorSquare.sg29569`, `OAI.UniversalTensorSquare.sg29582`, `OAI.UniversalTensorSquare.sg29583`, `OAI.UniversalTensorSquare.sg29589`, `OAI.UniversalTensorSquare.sg29590`, `OAI.UniversalTensorSquare.sg29594`, `OAI.UniversalTensorSquare.sg29609`, `OAI.UniversalTensorSquare.sg29610`, `OAI.UniversalTensorSquare.sg29616`, `OAI.UniversalTensorSquare.sg29633`, `OAI.UniversalTensorSquare.sg29634`, `OAI.UniversalTensorSquare.sg29636`, `OAI.UniversalTensorSquare.sg29639`, `OAI.UniversalTensorSquare.sg29640`, `OAI.UniversalTensorSquare.sg29646`, `OAI.UniversalTensorSquare.sg29647`, `OAI.UniversalTensorSquare.sg29650`, `OAI.UniversalTensorSquare.sg29652`, `OAI.UniversalTensorSquare.sg29663`, `OAI.UniversalTensorSquare.sg29667`, `OAI.UniversalTensorSquare.sg29681`, `OAI.UniversalTensorSquare.sg29684`, `OAI.UniversalTensorSquare.sg29685`, `OAI.UniversalTensorSquare.sg29694`, `OAI.UniversalTensorSquare.sg29696`, `OAI.UniversalTensorSquare.sg29697`, `OAI.UniversalTensorSquare.sg29700`, `OAI.UniversalTensorSquare.sg29704`, `OAI.UniversalTensorSquare.sg29705`, `OAI.UniversalTensorSquare.sg29706`, `OAI.UniversalTensorSquare.sg29711`, `OAI.UniversalTensorSquare.sg29712`, `OAI.UniversalTensorSquare.sg29723`, `OAI.UniversalTensorSquare.sg29725`, `OAI.UniversalTensorSquare.sg29726`, `OAI.UniversalTensorSquare.sg29731`, `OAI.UniversalTensorSquare.sg29733`, `OAI.UniversalTensorSquare.sg29734`, `OAI.UniversalTensorSquare.sg29735`, `OAI.UniversalTensorSquare.sg29737`, `OAI.UniversalTensorSquare.sg29738`, `OAI.UniversalTensorSquare.sg29739`, `OAI.UniversalTensorSquare.sg29740`, `OAI.UniversalTensorSquare.sg29744`, `OAI.UniversalTensorSquare.sg29745`, `OAI.UniversalTensorSquare.sg29746`, `OAI.UniversalTensorSquare.sg29749`, `OAI.UniversalTensorSquare.sg29750`, `OAI.UniversalTensorSquare.sg29754`, `OAI.UniversalTensorSquare.sg29755`, `OAI.UniversalTensorSquare.sg29756`, `OAI.UniversalTensorSquare.sg29779`, `OAI.UniversalTensorSquare.sg29785`, `OAI.UniversalTensorSquare.sg29800`, `OAI.UniversalTensorSquare.sg29801`, `OAI.UniversalTensorSquare.sg29807`, `OAI.UniversalTensorSquare.sg29808`, `OAI.UniversalTensorSquare.sg29813`, `OAI.UniversalTensorSquare.sg29824`, `OAI.UniversalTensorSquare.sg29825`, `OAI.UniversalTensorSquare.sg29844`, `OAI.UniversalTensorSquare.sg29847`, `OAI.UniversalTensorSquare.sg29848`, `OAI.UniversalTensorSquare.sg29854`, `OAI.UniversalTensorSquare.sg29855`, `OAI.UniversalTensorSquare.sg29864`, `OAI.UniversalTensorSquare.sg29869`, `OAI.UniversalTensorSquare.sg29883`, `OAI.UniversalTensorSquare.sg29919`, `OAI.UniversalTensorSquare.sg29924`, `OAI.UniversalTensorSquare.sg29928`, `OAI.UniversalTensorSquare.sg29929`, `OAI.UniversalTensorSquare.sg29949`, `OAI.UniversalTensorSquare.sg29951`, `OAI.UniversalTensorSquare.sg29981`, `OAI.UniversalTensorSquare.sg29994`, `OAI.UniversalTensorSquare.sg29999`, `OAI.UniversalTensorSquare.sg30004`, `OAI.UniversalTensorSquare.sg30034`, `OAI.UniversalTensorSquare.sg30036`, `OAI.UniversalTensorSquare.sg30039`, `OAI.UniversalTensorSquare.sg30042`, `OAI.UniversalTensorSquare.sg30045`, `OAI.UniversalTensorSquare.sg30046`, `OAI.UniversalTensorSquare.sg30047`, `OAI.UniversalTensorSquare.sg30048`, `OAI.UniversalTensorSquare.sg30058`, `OAI.UniversalTensorSquare.sg30062`, `OAI.UniversalTensorSquare.sg30064`, `OAI.UniversalTensorSquare.sg30067`, `OAI.UniversalTensorSquare.sg30071`, `OAI.UniversalTensorSquare.sg30074`, `OAI.UniversalTensorSquare.sg30075`, `OAI.UniversalTensorSquare.sg30076`, `OAI.UniversalTensorSquare.sg30077`, `OAI.UniversalTensorSquare.sg30078`, `OAI.UniversalTensorSquare.sg30085`, `OAI.UniversalTensorSquare.sg30088`, `OAI.UniversalTensorSquare.sg30094`, `OAI.UniversalTensorSquare.sg30095`, `OAI.UniversalTensorSquare.sg30099`, `OAI.UniversalTensorSquare.sg30122`, `OAI.UniversalTensorSquare.sg30124`, `OAI.UniversalTensorSquare.sg30125`, `OAI.UniversalTensorSquare.sg30127`, `OAI.UniversalTensorSquare.sg30144`, `OAI.UniversalTensorSquare.sg30151`, `OAI.UniversalTensorSquare.sg30154`, `OAI.UniversalTensorSquare.sg30157`, `OAI.UniversalTensorSquare.sg30165`, `OAI.UniversalTensorSquare.sg30176`, `OAI.UniversalTensorSquare.sg30179`, `OAI.UniversalTensorSquare.sg30182`, `OAI.UniversalTensorSquare.sg30183`, `OAI.UniversalTensorSquare.sg30184`, `OAI.UniversalTensorSquare.sg30188`, `OAI.UniversalTensorSquare.sg30192`, `OAI.UniversalTensorSquare.sg30196`, `OAI.UniversalTensorSquare.sg30200`, `OAI.UniversalTensorSquare.sg30203`, `OAI.UniversalTensorSquare.sg30204`, `OAI.UniversalTensorSquare.sg30218`, `OAI.UniversalTensorSquare.sg30233`, `OAI.UniversalTensorSquare.sg30234`, `OAI.UniversalTensorSquare.sg30235`, `OAI.UniversalTensorSquare.sg30240`, `OAI.UniversalTensorSquare.sg30241`, `OAI.UniversalTensorSquare.sg30244`, `OAI.UniversalTensorSquare.sg30246`, `OAI.UniversalTensorSquare.sg30247`, `OAI.UniversalTensorSquare.sg30249`, `OAI.UniversalTensorSquare.sg30255`, `OAI.UniversalTensorSquare.sg30257`, `OAI.UniversalTensorSquare.sg30258`, `OAI.UniversalTensorSquare.sg30261`, `OAI.UniversalTensorSquare.sg30269`, `OAI.UniversalTensorSquare.sg30271`, `OAI.UniversalTensorSquare.sg30274`, `OAI.UniversalTensorSquare.sg30277`, `OAI.UniversalTensorSquare.sg30278`, `OAI.UniversalTensorSquare.sg30283`, `OAI.UniversalTensorSquare.sg30286`, `OAI.UniversalTensorSquare.sg30289`, `OAI.UniversalTensorSquare.sg30292`, `OAI.UniversalTensorSquare.sg30293`, `OAI.UniversalTensorSquare.sg30300`, `OAI.UniversalTensorSquare.sg30308`, `OAI.UniversalTensorSquare.sg30311`, `OAI.UniversalTensorSquare.sg30312`, `OAI.UniversalTensorSquare.sg30315`, `OAI.UniversalTensorSquare.sg30320`, `OAI.UniversalTensorSquare.sg30324`, `OAI.UniversalTensorSquare.sg30336`, `OAI.UniversalTensorSquare.sg30337`, `OAI.UniversalTensorSquare.sg30343`, `OAI.UniversalTensorSquare.sg30347`, `OAI.UniversalTensorSquare.sg30350`, `OAI.UniversalTensorSquare.sg30352`, `OAI.UniversalTensorSquare.sg30358`, `OAI.UniversalTensorSquare.sg30360`, `OAI.UniversalTensorSquare.sg30372`, `OAI.UniversalTensorSquare.sg30377`, `OAI.UniversalTensorSquare.sg30378`, `OAI.UniversalTensorSquare.sg30382`, `OAI.UniversalTensorSquare.sg30383`, `OAI.UniversalTensorSquare.sg30389`, `OAI.UniversalTensorSquare.sg30393`, `OAI.UniversalTensorSquare.sg30400`, `OAI.UniversalTensorSquare.sg30401`, `OAI.UniversalTensorSquare.sg30429`, `OAI.UniversalTensorSquare.sg30430`, `OAI.UniversalTensorSquare.sg30433`, `OAI.UniversalTensorSquare.sg30435`, `OAI.UniversalTensorSquare.sg30442`, `OAI.UniversalTensorSquare.sg30443`, `OAI.UniversalTensorSquare.sg30445`, `OAI.UniversalTensorSquare.sg30446`, `OAI.UniversalTensorSquare.sg30449`, `OAI.UniversalTensorSquare.sg30450`, `OAI.UniversalTensorSquare.sg30459`, `OAI.UniversalTensorSquare.sg30460`, `OAI.UniversalTensorSquare.sg30474`, `OAI.UniversalTensorSquare.sg30479`, `OAI.UniversalTensorSquare.sg30480`, `OAI.UniversalTensorSquare.sg30481`, `OAI.UniversalTensorSquare.sg30499`, `OAI.UniversalTensorSquare.sg30500`, `OAI.UniversalTensorSquare.sg30505`, `OAI.UniversalTensorSquare.sg30506`, `OAI.UniversalTensorSquare.sg30509`, `OAI.UniversalTensorSquare.sg30517`, `OAI.UniversalTensorSquare.sg30520`, `OAI.UniversalTensorSquare.sg30528`, `OAI.UniversalTensorSquare.sg30535`, `OAI.UniversalTensorSquare.sg30536`, `OAI.UniversalTensorSquare.sg30538`, `OAI.UniversalTensorSquare.sg30539`, `OAI.UniversalTensorSquare.sg30541`, `OAI.UniversalTensorSquare.sg30548`, `OAI.UniversalTensorSquare.sg30563`, `OAI.UniversalTensorSquare.sg30576`, `OAI.UniversalTensorSquare.sg30579`, `OAI.UniversalTensorSquare.sg30585`, `OAI.UniversalTensorSquare.sg30588`, `OAI.UniversalTensorSquare.sg30589`, `OAI.UniversalTensorSquare.sg30592`, `OAI.UniversalTensorSquare.sg30593`, `OAI.UniversalTensorSquare.sg30595`, `OAI.UniversalTensorSquare.sg30620`, `OAI.UniversalTensorSquare.sg30668`, `OAI.UniversalTensorSquare.sg30691`, `OAI.UniversalTensorSquare.sg30697`, `OAI.UniversalTensorSquare.sg30698`, `OAI.UniversalTensorSquare.sg30699`, `OAI.UniversalTensorSquare.sg30740`, `OAI.UniversalTensorSquare.sg30741`, `OAI.UniversalTensorSquare.sg30747`, `OAI.UniversalTensorSquare.sg30750`, `OAI.UniversalTensorSquare.sg30753`, `OAI.UniversalTensorSquare.sg30754`, `OAI.UniversalTensorSquare.sg30756`, `OAI.UniversalTensorSquare.sg30780`, `OAI.UniversalTensorSquare.sg30783`, `OAI.UniversalTensorSquare.sg30786`, `OAI.UniversalTensorSquare.sg30794`, `OAI.UniversalTensorSquare.sg30796`, `OAI.UniversalTensorSquare.sg30805`, `OAI.UniversalTensorSquare.sg30806`, `OAI.UniversalTensorSquare.sg30809`, `OAI.UniversalTensorSquare.sg30813`, `OAI.UniversalTensorSquare.sg30816`, `OAI.UniversalTensorSquare.sg30817`, `OAI.UniversalTensorSquare.sg30821`, `OAI.UniversalTensorSquare.sg30825`, `OAI.UniversalTensorSquare.sg30829`, `OAI.UniversalTensorSquare.sg30832`, `OAI.UniversalTensorSquare.sg30838`, `OAI.UniversalTensorSquare.sg30841`, `OAI.UniversalTensorSquare.sg30846`, `OAI.UniversalTensorSquare.sg30847`, `OAI.UniversalTensorSquare.sg30849`, `OAI.UniversalTensorSquare.sg30853`, `OAI.UniversalTensorSquare.sg30855`, `OAI.UniversalTensorSquare.sg30870`, `OAI.UniversalTensorSquare.sg30872`, `OAI.UniversalTensorSquare.sg30875`, `OAI.UniversalTensorSquare.sg30876`, `OAI.UniversalTensorSquare.sg30879`, `OAI.UniversalTensorSquare.sg30884`, `OAI.UniversalTensorSquare.sg30888`, `OAI.UniversalTensorSquare.sg30899`, `OAI.UniversalTensorSquare.sg30901`, `OAI.UniversalTensorSquare.sg30907`, `OAI.UniversalTensorSquare.sg30911`, `OAI.UniversalTensorSquare.sg30913`, `OAI.UniversalTensorSquare.sg30922`, `OAI.UniversalTensorSquare.sg30924`, `OAI.UniversalTensorSquare.sg30925`, `OAI.UniversalTensorSquare.sg30926`, `OAI.UniversalTensorSquare.sg30940`, `OAI.UniversalTensorSquare.sg30945`, `OAI.UniversalTensorSquare.sg30947`, `OAI.UniversalTensorSquare.sg30949`, `OAI.UniversalTensorSquare.sg30951`, `OAI.UniversalTensorSquare.sg30952`, `OAI.UniversalTensorSquare.sg30955`, `OAI.UniversalTensorSquare.sg30961`, `OAI.UniversalTensorSquare.sg30962`, `OAI.UniversalTensorSquare.sg30963`, `OAI.UniversalTensorSquare.sg30965`, `OAI.UniversalTensorSquare.sg30970`, `OAI.UniversalTensorSquare.sg30972`, `OAI.UniversalTensorSquare.sg30973`, `OAI.UniversalTensorSquare.sg30980`, `OAI.UniversalTensorSquare.sg30981`, `OAI.UniversalTensorSquare.sg30989`, `OAI.UniversalTensorSquare.sg30991`, `OAI.UniversalTensorSquare.sg30992`, `OAI.UniversalTensorSquare.sg30993`, `OAI.UniversalTensorSquare.sg30997`, `OAI.UniversalTensorSquare.sg30999`, `OAI.UniversalTensorSquare.sg31003`, `OAI.UniversalTensorSquare.sg31005`, `OAI.UniversalTensorSquare.sg31020`, `OAI.UniversalTensorSquare.sg31022`, `OAI.UniversalTensorSquare.sg31024`, `OAI.UniversalTensorSquare.sg31030`, `OAI.UniversalTensorSquare.sg31032`, `OAI.UniversalTensorSquare.sg31042`, `OAI.UniversalTensorSquare.sg31058`, `OAI.UniversalTensorSquare.sg31060`, `OAI.UniversalTensorSquare.sg31072`, `OAI.UniversalTensorSquare.sg31076`, `OAI.UniversalTensorSquare.sg31077`, `OAI.UniversalTensorSquare.sg31078`, `OAI.UniversalTensorSquare.sg31082`, `OAI.UniversalTensorSquare.sg31085`, `OAI.UniversalTensorSquare.sg31086`, `OAI.UniversalTensorSquare.sg31087`, `OAI.UniversalTensorSquare.sg31091`, `OAI.UniversalTensorSquare.sg31094`, `OAI.UniversalTensorSquare.sg31095`, `OAI.UniversalTensorSquare.sg31096`, `OAI.UniversalTensorSquare.sg31100`, `OAI.UniversalTensorSquare.sg31102`, `OAI.UniversalTensorSquare.sg31138`, `OAI.UniversalTensorSquare.sg31140`, `OAI.UniversalTensorSquare.sg31141`, `OAI.UniversalTensorSquare.sg31145`, `OAI.UniversalTensorSquare.sg31147`, `OAI.UniversalTensorSquare.sg31149`, `OAI.UniversalTensorSquare.sg31153`, `OAI.UniversalTensorSquare.sg31155`, `OAI.UniversalTensorSquare.sg31156`, `OAI.UniversalTensorSquare.sg31157`, `OAI.UniversalTensorSquare.sg31159`, `OAI.UniversalTensorSquare.sg31161`, `OAI.UniversalTensorSquare.sg31162`, `OAI.UniversalTensorSquare.sg31163`, `OAI.UniversalTensorSquare.sg31180`, `OAI.UniversalTensorSquare.sg31184`, `OAI.UniversalTensorSquare.sg31196`, `OAI.UniversalTensorSquare.sg31200`, `OAI.UniversalTensorSquare.sg31203`, `OAI.UniversalTensorSquare.sg31206`, `OAI.UniversalTensorSquare.sg31208`, `OAI.UniversalTensorSquare.sg31210`, `OAI.UniversalTensorSquare.sg31211`, `OAI.UniversalTensorSquare.sg31212`, `OAI.UniversalTensorSquare.sg31213`, `OAI.UniversalTensorSquare.sg31214`, `OAI.UniversalTensorSquare.sg31215`, `OAI.UniversalTensorSquare.sg31216`, `OAI.UniversalTensorSquare.sg31217`, `OAI.UniversalTensorSquare.sg31218`, `OAI.UniversalTensorSquare.sg31219`, `OAI.UniversalTensorSquare.sg31220`, `OAI.UniversalTensorSquare.sg31221`, `OAI.UniversalTensorSquare.sg31223`, `OAI.UniversalTensorSquare.sg31224`, `OAI.UniversalTensorSquare.sg31225`, `OAI.UniversalTensorSquare.sg31228`, `OAI.UniversalTensorSquare.sg31229`, `OAI.UniversalTensorSquare.sg31231`, `OAI.UniversalTensorSquare.sg31233`, `OAI.UniversalTensorSquare.sg31236`, `OAI.UniversalTensorSquare.sg31238`, `OAI.UniversalTensorSquare.sg31240`, `OAI.UniversalTensorSquare.sg31241`, `OAI.UniversalTensorSquare.sg31242`, `OAI.UniversalTensorSquare.sg31244`, `OAI.UniversalTensorSquare.sg31245`, `OAI.UniversalTensorSquare.sg31252`, `OAI.UniversalTensorSquare.sg31254`, `OAI.UniversalTensorSquare.sg31270`, `OAI.UniversalTensorSquare.sg31272`, `OAI.UniversalTensorSquare.sg31275`, `OAI.UniversalTensorSquare.sg31280`, `OAI.UniversalTensorSquare.sg31281`, `OAI.UniversalTensorSquare.sg31286`, `OAI.UniversalTensorSquare.sg31288`, `OAI.UniversalTensorSquare.sg31291`, `OAI.UniversalTensorSquare.sg31294`, `OAI.UniversalTensorSquare.sg31296`, `OAI.UniversalTensorSquare.sg31298`, `OAI.UniversalTensorSquare.sg31302`, `OAI.UniversalTensorSquare.sg31303`, `OAI.UniversalTensorSquare.sg31308`, `OAI.UniversalTensorSquare.sg31311`, `OAI.UniversalTensorSquare.sg31313`, `OAI.UniversalTensorSquare.sg31316`, `OAI.UniversalTensorSquare.sg31317`, `OAI.UniversalTensorSquare.sg31318`, `OAI.UniversalTensorSquare.sg31319`, `OAI.UniversalTensorSquare.sg31320`, `OAI.UniversalTensorSquare.sg31322`, `OAI.UniversalTensorSquare.sg31325`, `OAI.UniversalTensorSquare.sg31329`, `OAI.UniversalTensorSquare.sg31333`, `OAI.UniversalTensorSquare.sg31334`, `OAI.UniversalTensorSquare.sg31335`, `OAI.UniversalTensorSquare.sg31337`, `OAI.UniversalTensorSquare.sg31339`, `OAI.UniversalTensorSquare.sg31345`, `OAI.UniversalTensorSquare.sg31346`, `OAI.UniversalTensorSquare.sg31348`, `OAI.UniversalTensorSquare.sg31357`, `OAI.UniversalTensorSquare.sg31360`, `OAI.UniversalTensorSquare.sg31361`, `OAI.UniversalTensorSquare.sg31371`, `OAI.UniversalTensorSquare.sg31372`, `OAI.UniversalTensorSquare.sg31374`, `OAI.UniversalTensorSquare.sg31375`, `OAI.UniversalTensorSquare.sg31377`, `OAI.UniversalTensorSquare.sg31379`, `OAI.UniversalTensorSquare.sg31385`, `OAI.UniversalTensorSquare.sg31386`, `OAI.UniversalTensorSquare.sg31388`, `OAI.UniversalTensorSquare.sg31391`, `OAI.UniversalTensorSquare.sg31397`, `OAI.UniversalTensorSquare.sg31398`, `OAI.UniversalTensorSquare.sg31399`, `OAI.UniversalTensorSquare.sg31404`, `OAI.UniversalTensorSquare.sg31408`, `OAI.UniversalTensorSquare.sg31414`, `OAI.UniversalTensorSquare.sg31415`, `OAI.UniversalTensorSquare.sg31417`, `OAI.UniversalTensorSquare.sg31421`, `OAI.UniversalTensorSquare.sg31422`, `OAI.UniversalTensorSquare.sg31423`, `OAI.UniversalTensorSquare.sg31424`, `OAI.UniversalTensorSquare.sg31449`, `OAI.UniversalTensorSquare.sg31455`, `OAI.UniversalTensorSquare.sg31463`, `OAI.UniversalTensorSquare.sg31467`, `OAI.UniversalTensorSquare.sg31469`, `OAI.UniversalTensorSquare.sg31472`, `OAI.UniversalTensorSquare.sg31474`, `OAI.UniversalTensorSquare.sg31476`, `OAI.UniversalTensorSquare.sg31483`, `OAI.UniversalTensorSquare.sg31495`, `OAI.UniversalTensorSquare.sg31505`, `OAI.UniversalTensorSquare.sg31506`, `OAI.UniversalTensorSquare.sg31512`, `OAI.UniversalTensorSquare.sg31515`, `OAI.UniversalTensorSquare.sg31517`, `OAI.UniversalTensorSquare.sg31519`, `OAI.UniversalTensorSquare.sg31526`, `OAI.UniversalTensorSquare.sg31529`, `OAI.UniversalTensorSquare.sg31530`, `OAI.UniversalTensorSquare.sg31531`, `OAI.UniversalTensorSquare.sg31533`, `OAI.UniversalTensorSquare.sg31543`, `OAI.UniversalTensorSquare.sg31556`, `OAI.UniversalTensorSquare.sg31557`, `OAI.UniversalTensorSquare.sg31589`, `OAI.UniversalTensorSquare.sg31596`, `OAI.UniversalTensorSquare.sg31604`, `OAI.UniversalTensorSquare.sg31605`, `OAI.UniversalTensorSquare.sg31606`, `OAI.UniversalTensorSquare.sg31607`, `OAI.UniversalTensorSquare.sg31608`, `OAI.UniversalTensorSquare.sg31639`, `OAI.UniversalTensorSquare.sg31654`, `OAI.UniversalTensorSquare.sg31666`, `OAI.UniversalTensorSquare.sg31674`, `OAI.UniversalTensorSquare.sg31675`, `OAI.UniversalTensorSquare.sg31697`, `OAI.UniversalTensorSquare.sg31708`, `OAI.UniversalTensorSquare.sg31728`, `OAI.UniversalTensorSquare.sg31730`, `OAI.UniversalTensorSquare.sg31732`, `OAI.UniversalTensorSquare.sg31749`, `OAI.UniversalTensorSquare.sg31767`, `OAI.UniversalTensorSquare.sg31776`, `OAI.UniversalTensorSquare.sg31778`, `OAI.UniversalTensorSquare.sg31779`, `OAI.UniversalTensorSquare.sg31780`, `OAI.UniversalTensorSquare.sg31790`, `OAI.UniversalTensorSquare.sg31791`, `OAI.UniversalTensorSquare.sg31792`, `OAI.UniversalTensorSquare.sg31800`, `OAI.UniversalTensorSquare.sg31801`, `OAI.UniversalTensorSquare.sg31844`, `OAI.UniversalTensorSquare.sg31845`, `OAI.UniversalTensorSquare.sg31854`, `OAI.UniversalTensorSquare.sg31887`, `OAI.UniversalTensorSquare.sg31896`, `OAI.UniversalTensorSquare.sg31901`, `OAI.UniversalTensorSquare.sg31910`, `OAI.UniversalTensorSquare.sg31920`, `OAI.UniversalTensorSquare.sg31924`, `OAI.UniversalTensorSquare.sg31960`, `OAI.UniversalTensorSquare.sg31969`, `OAI.UniversalTensorSquare.sg31974`, `OAI.UniversalTensorSquare.sg31979`, `OAI.UniversalTensorSquare.sg31982`, `OAI.UniversalTensorSquare.sg31983`, `OAI.UniversalTensorSquare.sg31984`, `OAI.UniversalTensorSquare.sg31996`, `OAI.UniversalTensorSquare.sg32009`, `OAI.UniversalTensorSquare.sg32022`, `OAI.UniversalTensorSquare.sg32024`, `OAI.UniversalTensorSquare.sg32025`, `OAI.UniversalTensorSquare.sg32056`, `OAI.UniversalTensorSquare.sg32063`, `OAI.UniversalTensorSquare.sg32066`, `OAI.UniversalTensorSquare.sg32068`, `OAI.UniversalTensorSquare.sg32072`, `OAI.UniversalTensorSquare.sg32073`, `OAI.UniversalTensorSquare.sg32079`, `OAI.UniversalTensorSquare.sg32080`, `OAI.UniversalTensorSquare.sg32081`, `OAI.UniversalTensorSquare.sg32086`, `OAI.UniversalTensorSquare.sg32092`, `OAI.UniversalTensorSquare.sg32103`, `OAI.UniversalTensorSquare.sg32107`, `OAI.UniversalTensorSquare.sg32144`, `OAI.UniversalTensorSquare.sg32145`, `OAI.UniversalTensorSquare.sg32152`, `OAI.UniversalTensorSquare.sg32167`, `OAI.UniversalTensorSquare.sg32168`, `OAI.UniversalTensorSquare.sg32170`, `OAI.UniversalTensorSquare.sg32172`, `OAI.UniversalTensorSquare.sg32173`, `OAI.UniversalTensorSquare.sg32175`, `OAI.UniversalTensorSquare.sg32177`, `OAI.UniversalTensorSquare.sg32178`, `OAI.UniversalTensorSquare.sg32179`, `OAI.UniversalTensorSquare.sg32180`, `OAI.UniversalTensorSquare.sg32182`, `OAI.UniversalTensorSquare.sg32183`, `OAI.UniversalTensorSquare.sg32185`, `OAI.UniversalTensorSquare.sg32187`, `OAI.UniversalTensorSquare.sg32189`, `OAI.UniversalTensorSquare.sg32190`, `OAI.UniversalTensorSquare.sg32191`, `OAI.UniversalTensorSquare.sg32192`, `OAI.UniversalTensorSquare.sg32193`, `OAI.UniversalTensorSquare.sg32194`, `OAI.UniversalTensorSquare.sg32195`, `OAI.UniversalTensorSquare.sg32196`, `OAI.UniversalTensorSquare.sg32197`, `OAI.UniversalTensorSquare.sg32198`, `OAI.UniversalTensorSquare.sg32202`, `OAI.UniversalTensorSquare.sg32205`, `OAI.UniversalTensorSquare.sg32214`, `OAI.UniversalTensorSquare.sg32220`, `OAI.UniversalTensorSquare.sg32227`, `OAI.UniversalTensorSquare.sg32228`, `OAI.UniversalTensorSquare.sg32229`, `OAI.UniversalTensorSquare.sg32233`, `OAI.UniversalTensorSquare.sg32235`, `OAI.UniversalTensorSquare.sg32237`, `OAI.UniversalTensorSquare.sg32239`, `OAI.UniversalTensorSquare.sg32240`, `OAI.UniversalTensorSquare.sg32243`, `OAI.UniversalTensorSquare.sg32249`, `OAI.UniversalTensorSquare.sg32250`, `OAI.UniversalTensorSquare.sg32251`, `OAI.UniversalTensorSquare.sg32255`, `OAI.UniversalTensorSquare.sg32275`, `OAI.UniversalTensorSquare.sg32277`, `OAI.UniversalTensorSquare.sg32297`, `OAI.UniversalTensorSquare.sg32299`, `OAI.UniversalTensorSquare.sg32306`, `OAI.UniversalTensorSquare.sg32319`, `OAI.UniversalTensorSquare.sg32321`, `OAI.UniversalTensorSquare.sg32323`, `OAI.UniversalTensorSquare.sg32347`, `OAI.UniversalTensorSquare.sg32348`, `OAI.UniversalTensorSquare.sg32349`, `OAI.UniversalTensorSquare.sg32351`, `OAI.UniversalTensorSquare.sg32352`, `OAI.UniversalTensorSquare.sg32355`, `OAI.UniversalTensorSquare.sg32358`, `OAI.UniversalTensorSquare.sg32363`, `OAI.UniversalTensorSquare.sg32366`, `OAI.UniversalTensorSquare.sg32372`, `OAI.UniversalTensorSquare.sg32374`, `OAI.UniversalTensorSquare.sg32386`, `OAI.UniversalTensorSquare.sg32389`, `OAI.UniversalTensorSquare.sg32390`, `OAI.UniversalTensorSquare.sg32391`, `OAI.UniversalTensorSquare.sg32392`, `OAI.UniversalTensorSquare.sg32403`, `OAI.UniversalTensorSquare.sg32405`, `OAI.UniversalTensorSquare.sg32406`, `OAI.UniversalTensorSquare.sg32418`, `OAI.UniversalTensorSquare.sg32423`, `OAI.UniversalTensorSquare.sg32424`, `OAI.UniversalTensorSquare.sg32425`, `OAI.UniversalTensorSquare.sg32426`, `OAI.UniversalTensorSquare.sg32429`, `OAI.UniversalTensorSquare.sg32430`, `OAI.UniversalTensorSquare.sg32431`, `OAI.UniversalTensorSquare.sg32432`, `OAI.UniversalTensorSquare.sg32433`, `OAI.UniversalTensorSquare.sg32441`, `OAI.UniversalTensorSquare.sg32451`, `OAI.UniversalTensorSquare.sg32453`, `OAI.UniversalTensorSquare.sg32455`, `OAI.UniversalTensorSquare.sg32459`, `OAI.UniversalTensorSquare.sg32463`, `OAI.UniversalTensorSquare.sg32465`, `OAI.UniversalTensorSquare.sg32471`, `OAI.UniversalTensorSquare.sg32472`, `OAI.UniversalTensorSquare.sg32482`, `OAI.UniversalTensorSquare.sg32512`, `OAI.UniversalTensorSquare.sg32513`, `OAI.UniversalTensorSquare.sg32514`, `OAI.UniversalTensorSquare.sg32516`, `OAI.UniversalTensorSquare.sg32517`, `OAI.UniversalTensorSquare.sg32519`, `OAI.UniversalTensorSquare.sg32530`, `OAI.UniversalTensorSquare.sg32536`, `OAI.UniversalTensorSquare.sg32542`, `OAI.UniversalTensorSquare.sg32553`, `OAI.UniversalTensorSquare.sg32555`, `OAI.UniversalTensorSquare.sg32557`, `OAI.UniversalTensorSquare.sg32558`, `OAI.UniversalTensorSquare.sg32560`, `OAI.UniversalTensorSquare.sg32563`, `OAI.UniversalTensorSquare.sg32564`, `OAI.UniversalTensorSquare.sg32568`, `OAI.UniversalTensorSquare.sg32569`, `OAI.UniversalTensorSquare.sg32572`, `OAI.UniversalTensorSquare.sg32578`, `OAI.UniversalTensorSquare.sg32580`, `OAI.UniversalTensorSquare.sg32589`, `OAI.UniversalTensorSquare.sg32590`, `OAI.UniversalTensorSquare.sg32593`, `OAI.UniversalTensorSquare.sg32603`, `OAI.UniversalTensorSquare.sg32607`, `OAI.UniversalTensorSquare.sg32609`, `OAI.UniversalTensorSquare.sg32614`, `OAI.UniversalTensorSquare.sg32616`, `OAI.UniversalTensorSquare.sg32625`, `OAI.UniversalTensorSquare.sg32626`, `OAI.UniversalTensorSquare.sg32627`, `OAI.UniversalTensorSquare.sg32628`, `OAI.UniversalTensorSquare.sg32635`, `OAI.UniversalTensorSquare.sg32636`, `OAI.UniversalTensorSquare.sg32639`, `OAI.UniversalTensorSquare.sg32641`, `OAI.UniversalTensorSquare.sg32646`, `OAI.UniversalTensorSquare.sg32647`, `OAI.UniversalTensorSquare.sg32648`, `OAI.UniversalTensorSquare.sg32652`, `OAI.UniversalTensorSquare.sg32653`, `OAI.UniversalTensorSquare.sg32654`, `OAI.UniversalTensorSquare.sg32657`, `OAI.UniversalTensorSquare.sg32659`, `OAI.UniversalTensorSquare.sg32660`, `OAI.UniversalTensorSquare.sg32666`, `OAI.UniversalTensorSquare.sg32672`, `OAI.UniversalTensorSquare.sg32673`, `OAI.UniversalTensorSquare.sg32674`, `OAI.UniversalTensorSquare.sg32676`, `OAI.UniversalTensorSquare.sg32677`, `OAI.UniversalTensorSquare.sg32679`, `OAI.UniversalTensorSquare.sg32681`, `OAI.UniversalTensorSquare.sg32684`, `OAI.UniversalTensorSquare.sg32687`, `OAI.UniversalTensorSquare.sg32689`, `OAI.UniversalTensorSquare.sg32694`, `OAI.UniversalTensorSquare.sg32695`, `OAI.UniversalTensorSquare.sg32696`, `OAI.UniversalTensorSquare.sg32697`, `OAI.UniversalTensorSquare.sg32699`, `OAI.UniversalTensorSquare.sg32700`, `OAI.UniversalTensorSquare.sg32705`, `OAI.UniversalTensorSquare.sg32706`, `OAI.UniversalTensorSquare.sg32707`, `OAI.UniversalTensorSquare.sg32710`, `OAI.UniversalTensorSquare.sg32711`, `OAI.UniversalTensorSquare.sg32712`, `OAI.UniversalTensorSquare.sg32713`, `OAI.UniversalTensorSquare.sg32715`, `OAI.UniversalTensorSquare.sg32766`, `OAI.UniversalTensorSquare.sg32771`, `OAI.UniversalTensorSquare.sg32774`, `OAI.UniversalTensorSquare.sg32787`, `OAI.UniversalTensorSquare.sg32810`, `OAI.UniversalTensorSquare.sg32816`, `OAI.UniversalTensorSquare.sg32821`, `OAI.UniversalTensorSquare.sg32822`, `OAI.UniversalTensorSquare.sg32823`, `OAI.UniversalTensorSquare.sg32833`, `OAI.UniversalTensorSquare.sg32848`, `OAI.UniversalTensorSquare.sg32854`, `OAI.UniversalTensorSquare.sg32901`, `OAI.UniversalTensorSquare.sg32904`, `OAI.UniversalTensorSquare.sg32910`, `OAI.UniversalTensorSquare.sg32912`, `OAI.UniversalTensorSquare.sg32914`, `OAI.UniversalTensorSquare.sg32924`, `OAI.UniversalTensorSquare.sg32926`, `OAI.UniversalTensorSquare.sg32953`, `OAI.UniversalTensorSquare.sg32954`, `OAI.UniversalTensorSquare.sg32957`, `OAI.UniversalTensorSquare.sg32961`, `OAI.UniversalTensorSquare.sg32963`, `OAI.UniversalTensorSquare.sg32967`, `OAI.UniversalTensorSquare.sg32968`, `OAI.UniversalTensorSquare.sg32970`, `OAI.UniversalTensorSquare.sg32974`, `OAI.UniversalTensorSquare.sg32976`, `OAI.UniversalTensorSquare.sg32981`, `OAI.UniversalTensorSquare.sg32990`, `OAI.UniversalTensorSquare.sg32991`, `OAI.UniversalTensorSquare.sg32992`, `OAI.UniversalTensorSquare.sg32994`, `OAI.UniversalTensorSquare.sg32998`, `OAI.UniversalTensorSquare.sg33001`, `OAI.UniversalTensorSquare.sg33009`, `OAI.UniversalTensorSquare.sg33011`, `OAI.UniversalTensorSquare.sg33015`, `OAI.UniversalTensorSquare.sg33016`, `OAI.UniversalTensorSquare.sg33018`, `OAI.UniversalTensorSquare.sg33019`, `OAI.UniversalTensorSquare.sg33023`, `OAI.UniversalTensorSquare.sg33054`, `OAI.UniversalTensorSquare.sg33056`, `OAI.UniversalTensorSquare.sg33057`, `OAI.UniversalTensorSquare.sg33060`, `OAI.UniversalTensorSquare.sg33061`, `OAI.UniversalTensorSquare.sg33066`, `OAI.UniversalTensorSquare.sg33073`, `OAI.UniversalTensorSquare.sg33079`, `OAI.UniversalTensorSquare.sg33086`, `OAI.UniversalTensorSquare.sg33090`, `OAI.UniversalTensorSquare.sg33092`, `OAI.UniversalTensorSquare.sg33100`, `OAI.UniversalTensorSquare.sg33110`, `OAI.UniversalTensorSquare.sg33142`, `OAI.UniversalTensorSquare.sg33144`, `OAI.UniversalTensorSquare.sg33152`, `OAI.UniversalTensorSquare.sg33158`, `OAI.UniversalTensorSquare.sg33173`, `OAI.UniversalTensorSquare.sg33198`, `OAI.UniversalTensorSquare.sg33200`, `OAI.UniversalTensorSquare.sg33207`, `OAI.UniversalTensorSquare.sg33215`, `OAI.UniversalTensorSquare.sg33217`, `OAI.UniversalTensorSquare.sg33232`, `OAI.UniversalTensorSquare.sg33234`, `OAI.UniversalTensorSquare.sg33237`, `OAI.UniversalTensorSquare.sg33239`, `OAI.UniversalTensorSquare.sg33244`, `OAI.UniversalTensorSquare.sg33246`, `OAI.UniversalTensorSquare.sg33275`, `OAI.UniversalTensorSquare.sg33280`, `OAI.UniversalTensorSquare.sg33283`, `OAI.UniversalTensorSquare.sg33292`, `OAI.UniversalTensorSquare.sg33310`, `OAI.UniversalTensorSquare.sg33315`, `OAI.UniversalTensorSquare.sg33317`, `OAI.UniversalTensorSquare.sg33325`, `OAI.UniversalTensorSquare.sg33330`, `OAI.UniversalTensorSquare.sg33332`, `OAI.UniversalTensorSquare.sg33345`, `OAI.UniversalTensorSquare.sg33359`, `OAI.UniversalTensorSquare.sg33368`, `OAI.UniversalTensorSquare.sg33374`, `OAI.UniversalTensorSquare.sg33399`, `OAI.UniversalTensorSquare.sg33401`, `OAI.UniversalTensorSquare.sg33402`, `OAI.UniversalTensorSquare.sg33406`, `OAI.UniversalTensorSquare.sg33408`, `OAI.UniversalTensorSquare.sg33429`, `OAI.UniversalTensorSquare.sg33430`, `OAI.UniversalTensorSquare.sg33434`, `OAI.UniversalTensorSquare.sg33436`, `OAI.UniversalTensorSquare.sg33439`, `OAI.UniversalTensorSquare.sg33441`, `OAI.UniversalTensorSquare.sg33455`, `OAI.UniversalTensorSquare.sg33457`, `OAI.UniversalTensorSquare.sg33460`, `OAI.UniversalTensorSquare.sg33461`, `OAI.UniversalTensorSquare.sg33462`, `OAI.UniversalTensorSquare.sg33465`, `OAI.UniversalTensorSquare.sg33470`, `OAI.UniversalTensorSquare.sg33472`, `OAI.UniversalTensorSquare.sg33474`, `OAI.UniversalTensorSquare.sg33492`, `OAI.UniversalTensorSquare.sg33495`, `OAI.UniversalTensorSquare.sg33518`, `OAI.UniversalTensorSquare.sg33526`, `OAI.UniversalTensorSquare.sg33527`, `OAI.UniversalTensorSquare.sg33536`, `OAI.UniversalTensorSquare.sg33540`, `OAI.UniversalTensorSquare.sg33545`, `OAI.UniversalTensorSquare.sg33553`, `OAI.UniversalTensorSquare.sg33558`, `OAI.UniversalTensorSquare.sg33566`, `OAI.UniversalTensorSquare.sg33568`, `OAI.UniversalTensorSquare.sg33580`, `OAI.UniversalTensorSquare.sg33584`, `OAI.UniversalTensorSquare.sg33588`, `OAI.UniversalTensorSquare.sg33589`, `OAI.UniversalTensorSquare.sg33590`, `OAI.UniversalTensorSquare.sg33591`, `OAI.UniversalTensorSquare.sg33592`, `OAI.UniversalTensorSquare.sg33595`, `OAI.UniversalTensorSquare.sg33603`, `OAI.UniversalTensorSquare.sg33604`, `OAI.UniversalTensorSquare.sg33605`, `OAI.UniversalTensorSquare.sg33606`, `OAI.UniversalTensorSquare.sg33608`, `OAI.UniversalTensorSquare.sg33609`, `OAI.UniversalTensorSquare.sg33610`, `OAI.UniversalTensorSquare.sg33611`, `OAI.UniversalTensorSquare.sg33612`, `OAI.UniversalTensorSquare.sg33613`, `OAI.UniversalTensorSquare.sg33615`, `OAI.UniversalTensorSquare.sg33627`, `OAI.UniversalTensorSquare.sg33628`, `OAI.UniversalTensorSquare.sg33632`, `OAI.UniversalTensorSquare.sg33634`, `OAI.UniversalTensorSquare.sg33635`, `OAI.UniversalTensorSquare.sg33644`, `OAI.UniversalTensorSquare.sg33645`, `OAI.UniversalTensorSquare.sg33646`, `OAI.UniversalTensorSquare.sg33655`, `OAI.UniversalTensorSquare.sg33661`, `OAI.UniversalTensorSquare.sg33663`, `OAI.UniversalTensorSquare.sg33678`, `OAI.UniversalTensorSquare.sg33686`, `OAI.UniversalTensorSquare.sg33690`, `OAI.UniversalTensorSquare.sg33692`, `OAI.UniversalTensorSquare.sg33701`, `OAI.UniversalTensorSquare.sg33704`, `OAI.UniversalTensorSquare.sg33706`, `OAI.UniversalTensorSquare.sg33722`, `OAI.UniversalTensorSquare.sg33727`, `OAI.UniversalTensorSquare.sg33741`, `OAI.UniversalTensorSquare.sg33743`, `OAI.UniversalTensorSquare.sg33748`, `OAI.UniversalTensorSquare.sg33756`, `OAI.UniversalTensorSquare.sg33757`, `OAI.UniversalTensorSquare.sg33758`, `OAI.UniversalTensorSquare.sg33763`, `OAI.UniversalTensorSquare.sg33764`, `OAI.UniversalTensorSquare.sg33766`, `OAI.UniversalTensorSquare.sg33768`, `OAI.UniversalTensorSquare.sg33769`, `OAI.UniversalTensorSquare.sg33772`, `OAI.UniversalTensorSquare.sg33774`, `OAI.UniversalTensorSquare.sg33776`, `OAI.UniversalTensorSquare.sg33786`, `OAI.UniversalTensorSquare.sg33794`, `OAI.UniversalTensorSquare.sg33795`, `OAI.UniversalTensorSquare.sg33796`, `OAI.UniversalTensorSquare.sg33799`, `OAI.UniversalTensorSquare.sg33803`, `OAI.UniversalTensorSquare.sg33818`, `OAI.UniversalTensorSquare.sg33820`, `OAI.UniversalTensorSquare.sg33821`, `OAI.UniversalTensorSquare.sg33831`, `OAI.UniversalTensorSquare.sg33832`, `OAI.UniversalTensorSquare.sg33833`, `OAI.UniversalTensorSquare.sg33835`, `OAI.UniversalTensorSquare.sg33836`, `OAI.UniversalTensorSquare.sg33838`, `OAI.UniversalTensorSquare.sg33839`, `OAI.UniversalTensorSquare.sg33843`, `OAI.UniversalTensorSquare.sg33848`, `OAI.UniversalTensorSquare.sg33849`, `OAI.UniversalTensorSquare.sg33855`, `OAI.UniversalTensorSquare.sg33857`, `OAI.UniversalTensorSquare.sg33859`, `OAI.UniversalTensorSquare.sg33863`, `OAI.UniversalTensorSquare.sg33864`, `OAI.UniversalTensorSquare.sg33865`, `OAI.UniversalTensorSquare.sg33868`, `OAI.UniversalTensorSquare.sg33872`, `OAI.UniversalTensorSquare.sg33873`, `OAI.UniversalTensorSquare.sg33874`, `OAI.UniversalTensorSquare.sg33876`, `OAI.UniversalTensorSquare.sg33877`, `OAI.UniversalTensorSquare.sg33879`, `OAI.UniversalTensorSquare.sg33880`, `OAI.UniversalTensorSquare.sg33882`, `OAI.UniversalTensorSquare.sg33887`, `OAI.UniversalTensorSquare.sg33893`, `OAI.UniversalTensorSquare.sg33895`, `OAI.UniversalTensorSquare.sg33896`, `OAI.UniversalTensorSquare.sg33898`, `OAI.UniversalTensorSquare.sg33900`, `OAI.UniversalTensorSquare.sg33902`, `OAI.UniversalTensorSquare.sg33904`, `OAI.UniversalTensorSquare.sg33908`, `OAI.UniversalTensorSquare.sg33909`, `OAI.UniversalTensorSquare.sg33913`, `OAI.UniversalTensorSquare.sg33917`, `OAI.UniversalTensorSquare.sg33919`, `OAI.UniversalTensorSquare.sg33921`, `OAI.UniversalTensorSquare.sg33923`, `OAI.UniversalTensorSquare.sg33924`, `OAI.UniversalTensorSquare.sg33925`, `OAI.UniversalTensorSquare.sg33933`, `OAI.UniversalTensorSquare.sg33934`, `OAI.UniversalTensorSquare.sg33935`, `OAI.UniversalTensorSquare.sg33938`, `OAI.UniversalTensorSquare.sg33939`, `OAI.UniversalTensorSquare.sg33940`, `OAI.UniversalTensorSquare.sg33945`, `OAI.UniversalTensorSquare.sg33953`, `OAI.UniversalTensorSquare.sg33954`, `OAI.UniversalTensorSquare.sg33966`, `OAI.UniversalTensorSquare.sg33969`, `OAI.UniversalTensorSquare.sg33971`, `OAI.UniversalTensorSquare.sg33972`, `OAI.UniversalTensorSquare.sg33973`, `OAI.UniversalTensorSquare.sg33975`, `OAI.UniversalTensorSquare.sg33994`, `OAI.UniversalTensorSquare.sg33995`, `OAI.UniversalTensorSquare.sg34003`, `OAI.UniversalTensorSquare.sg34012`, `OAI.UniversalTensorSquare.sg34013`, `OAI.UniversalTensorSquare.sg34033`, `OAI.UniversalTensorSquare.sg34035`, `OAI.UniversalTensorSquare.sg34052`, `OAI.UniversalTensorSquare.sg34062`, `OAI.UniversalTensorSquare.sg34084`, `OAI.UniversalTensorSquare.sg34085`, `OAI.UniversalTensorSquare.sg34089`, `OAI.UniversalTensorSquare.sg34092`, `OAI.UniversalTensorSquare.sg34093`, `OAI.UniversalTensorSquare.sg34095`, `OAI.UniversalTensorSquare.sg34096`, `OAI.UniversalTensorSquare.sg34105`, `OAI.UniversalTensorSquare.sg34112`, `OAI.UniversalTensorSquare.sg34115`, `OAI.UniversalTensorSquare.sg34117`, `OAI.UniversalTensorSquare.sg34128`, `OAI.UniversalTensorSquare.sg34132`, `OAI.UniversalTensorSquare.sg34139`, `OAI.UniversalTensorSquare.sg34140`, `OAI.UniversalTensorSquare.sg34142`, `OAI.UniversalTensorSquare.sg34153`, `OAI.UniversalTensorSquare.sg34156`, `OAI.UniversalTensorSquare.sg34158`, `OAI.UniversalTensorSquare.sg34164`, `OAI.UniversalTensorSquare.sg34170`, `OAI.UniversalTensorSquare.sg34171`, `OAI.UniversalTensorSquare.sg34172`, `OAI.UniversalTensorSquare.sg34174`, `OAI.UniversalTensorSquare.sg34193`, `OAI.UniversalTensorSquare.sg34195`, `OAI.UniversalTensorSquare.sg34203`, `OAI.UniversalTensorSquare.sg34208`, `OAI.UniversalTensorSquare.sg34239`, `OAI.UniversalTensorSquare.sg34241`, `OAI.UniversalTensorSquare.sg34245`, `OAI.UniversalTensorSquare.sg34263`, `OAI.UniversalTensorSquare.sg34284`, `OAI.UniversalTensorSquare.sg34289`, `OAI.UniversalTensorSquare.sg34290`, `OAI.UniversalTensorSquare.sg34291`, `OAI.UniversalTensorSquare.sg34293`, `OAI.UniversalTensorSquare.sg34294`, `OAI.UniversalTensorSquare.sg34296`, `OAI.UniversalTensorSquare.sg34297`, `OAI.UniversalTensorSquare.sg34298`, `OAI.UniversalTensorSquare.sg34310`, `OAI.UniversalTensorSquare.sg34311`, `OAI.UniversalTensorSquare.sg34312`, `OAI.UniversalTensorSquare.sg34314`, `OAI.UniversalTensorSquare.sg34315`, `OAI.UniversalTensorSquare.sg34317`, `OAI.UniversalTensorSquare.sg34318`, `OAI.UniversalTensorSquare.sg34326`, `OAI.UniversalTensorSquare.sg34329`, `OAI.UniversalTensorSquare.sg34333`, `OAI.UniversalTensorSquare.sg34336`, `OAI.UniversalTensorSquare.sg34340`, `OAI.UniversalTensorSquare.sg34342`, `OAI.UniversalTensorSquare.sg34348`, `OAI.UniversalTensorSquare.sg34357`, `OAI.UniversalTensorSquare.sg34362`, `OAI.UniversalTensorSquare.sg34364`, `OAI.UniversalTensorSquare.sg34366`, `OAI.UniversalTensorSquare.sg34368`, `OAI.UniversalTensorSquare.sg34386`, `OAI.UniversalTensorSquare.sg34393`, `OAI.UniversalTensorSquare.sg34395`, `OAI.UniversalTensorSquare.sg34399`, `OAI.UniversalTensorSquare.sg34417`, `OAI.UniversalTensorSquare.sg34425`, `OAI.UniversalTensorSquare.sg34427`, `OAI.UniversalTensorSquare.sg34429`, `OAI.UniversalTensorSquare.sg34431`, `OAI.UniversalTensorSquare.sg34445`, `OAI.UniversalTensorSquare.sg34450`, `OAI.UniversalTensorSquare.sg34460`, `OAI.UniversalTensorSquare.sg34464`, `OAI.UniversalTensorSquare.sg34471`, `OAI.UniversalTensorSquare.sg34472`, `OAI.UniversalTensorSquare.sg34473`, `OAI.UniversalTensorSquare.sg34474`, `OAI.UniversalTensorSquare.sg34475`, `OAI.UniversalTensorSquare.sg34476`, `OAI.UniversalTensorSquare.sg34477`, `OAI.UniversalTensorSquare.sg34479`, `OAI.UniversalTensorSquare.sg34480`, `OAI.UniversalTensorSquare.sg34483`, `OAI.UniversalTensorSquare.sg34485`, `OAI.UniversalTensorSquare.sg34487`, `OAI.UniversalTensorSquare.sg34494`, `OAI.UniversalTensorSquare.sg34498`, `OAI.UniversalTensorSquare.sg34503`, `OAI.UniversalTensorSquare.sg34508`, `OAI.UniversalTensorSquare.sg34510`, `OAI.UniversalTensorSquare.sg34512`, `OAI.UniversalTensorSquare.sg34514`, `OAI.UniversalTensorSquare.sg34515`, `OAI.UniversalTensorSquare.sg34518`, `OAI.UniversalTensorSquare.sg34521`, `OAI.UniversalTensorSquare.sg34525`, `OAI.UniversalTensorSquare.sg34527`, `OAI.UniversalTensorSquare.sg34530`, `OAI.UniversalTensorSquare.sg34533`, `OAI.UniversalTensorSquare.sg34535`, `OAI.UniversalTensorSquare.sg34537`, `OAI.UniversalTensorSquare.sg34539`, `OAI.UniversalTensorSquare.sg34540`, `OAI.UniversalTensorSquare.sg34559`, `OAI.UniversalTensorSquare.sg34561`, `OAI.UniversalTensorSquare.sg34562`, `OAI.UniversalTensorSquare.sg34573`, `OAI.UniversalTensorSquare.sg34579`, `OAI.UniversalTensorSquare.sg34582`, `OAI.UniversalTensorSquare.sg34583`, `OAI.UniversalTensorSquare.sg34588`, `OAI.UniversalTensorSquare.sg34589`, `OAI.UniversalTensorSquare.sg34595`, `OAI.UniversalTensorSquare.sg34596`, `OAI.UniversalTensorSquare.sg34603`, `OAI.UniversalTensorSquare.sg34604`, `OAI.UniversalTensorSquare.sg34607`, `OAI.UniversalTensorSquare.sg34609`, `OAI.UniversalTensorSquare.sg34610`, `OAI.UniversalTensorSquare.sg34642`, `OAI.UniversalTensorSquare.sg34644`, `OAI.UniversalTensorSquare.sg34646`, `OAI.UniversalTensorSquare.sg34675`, `OAI.UniversalTensorSquare.sg34693`, `OAI.UniversalTensorSquare.sg34698`, `OAI.UniversalTensorSquare.sg34701`, `OAI.UniversalTensorSquare.sg34706`, `OAI.UniversalTensorSquare.sg34709`, `OAI.UniversalTensorSquare.sg34731`, `OAI.UniversalTensorSquare.sg34734`, `OAI.UniversalTensorSquare.sg34736`, `OAI.UniversalTensorSquare.sg34746`, `OAI.UniversalTensorSquare.sg34787`, `OAI.UniversalTensorSquare.sg34792`, `OAI.UniversalTensorSquare.sg34795`, `OAI.UniversalTensorSquare.sg34797`, `OAI.UniversalTensorSquare.sg34807`, `OAI.UniversalTensorSquare.sg34824`, `OAI.UniversalTensorSquare.sg34841`, `OAI.UniversalTensorSquare.sg34880`, `OAI.UniversalTensorSquare.sg34882`, `OAI.UniversalTensorSquare.sg34886`, `OAI.UniversalTensorSquare.sg34888`, `OAI.UniversalTensorSquare.sg34892`, `OAI.UniversalTensorSquare.sg34895`, `OAI.UniversalTensorSquare.sg34896`, `OAI.UniversalTensorSquare.sg34897`, `OAI.UniversalTensorSquare.sg34898`, `OAI.UniversalTensorSquare.sg34901`, `OAI.UniversalTensorSquare.sg34904`, `OAI.UniversalTensorSquare.sg34946`, `OAI.UniversalTensorSquare.sg34952`, `OAI.UniversalTensorSquare.sg34959`, `OAI.UniversalTensorSquare.sg34962`, `OAI.UniversalTensorSquare.sg34964`, `OAI.UniversalTensorSquare.sg34980`, `OAI.UniversalTensorSquare.sg34983`, `OAI.UniversalTensorSquare.sg34985`, `OAI.UniversalTensorSquare.sg35003`, `OAI.UniversalTensorSquare.sg35005`, `OAI.UniversalTensorSquare.sg35011`, `OAI.UniversalTensorSquare.sg35013`, `OAI.UniversalTensorSquare.sg35020`, `OAI.UniversalTensorSquare.sg35033`, `OAI.UniversalTensorSquare.sg35037`, `OAI.UniversalTensorSquare.sg35039`, `OAI.UniversalTensorSquare.sg35041`, `OAI.UniversalTensorSquare.sg35045`, `OAI.UniversalTensorSquare.sg35047`, `OAI.UniversalTensorSquare.sg35051`, `OAI.UniversalTensorSquare.sg35058`, `OAI.UniversalTensorSquare.sg35082`, `OAI.UniversalTensorSquare.sg35085`, `OAI.UniversalTensorSquare.sg35086`, `OAI.UniversalTensorSquare.sg35104`, `OAI.UniversalTensorSquare.sg35113`, `OAI.UniversalTensorSquare.sg35116`, `OAI.UniversalTensorSquare.sg35123`, `OAI.UniversalTensorSquare.sg35130`, `OAI.UniversalTensorSquare.sg35151`, `OAI.UniversalTensorSquare.sg35156`, `OAI.UniversalTensorSquare.sg35164`, `OAI.UniversalTensorSquare.sg35181`, `OAI.UniversalTensorSquare.sg35183`, `OAI.UniversalTensorSquare.sg35209`, `OAI.UniversalTensorSquare.sg35227`, `OAI.UniversalTensorSquare.sg35235`, `OAI.UniversalTensorSquare.sg35256`, `OAI.UniversalTensorSquare.sg35270`, `OAI.UniversalTensorSquare.sg35275`, `OAI.UniversalTensorSquare.sg35276`, `OAI.UniversalTensorSquare.sg35278`, `OAI.UniversalTensorSquare.sg35280`, `OAI.UniversalTensorSquare.sg35288`, `OAI.UniversalTensorSquare.sg35294`, `OAI.UniversalTensorSquare.sg35298`, `OAI.UniversalTensorSquare.sg35303`, `OAI.UniversalTensorSquare.sg35316`, `OAI.UniversalTensorSquare.sg35323`, `OAI.UniversalTensorSquare.sg35325`, `OAI.UniversalTensorSquare.sg35326`, `OAI.UniversalTensorSquare.sg35330`, `OAI.UniversalTensorSquare.sg35332`, `OAI.UniversalTensorSquare.sg35336`, `OAI.UniversalTensorSquare.sg35362`, `OAI.UniversalTensorSquare.sg35365`, `OAI.UniversalTensorSquare.sg35371`, `OAI.UniversalTensorSquare.sg35373`, `OAI.UniversalTensorSquare.sg35376`, `OAI.UniversalTensorSquare.sg35377`, `OAI.UniversalTensorSquare.sg35378`, `OAI.UniversalTensorSquare.sg35382`, `OAI.UniversalTensorSquare.sg35384`, `OAI.UniversalTensorSquare.sg35390`, `OAI.UniversalTensorSquare.sg35391`, `OAI.UniversalTensorSquare.sg35392`, `OAI.UniversalTensorSquare.sg35396`, `OAI.UniversalTensorSquare.sg35397`, `OAI.UniversalTensorSquare.sg35399`, `OAI.UniversalTensorSquare.sg35400`, `OAI.UniversalTensorSquare.sg35402`, `OAI.UniversalTensorSquare.sg35403`, `OAI.UniversalTensorSquare.sg35404`, `OAI.UniversalTensorSquare.sg35417`, `OAI.UniversalTensorSquare.sg35423`, `OAI.UniversalTensorSquare.sg35428`, `OAI.UniversalTensorSquare.sg35429`, `OAI.UniversalTensorSquare.sg35434`, `OAI.UniversalTensorSquare.sg35446`, `OAI.UniversalTensorSquare.sg35456`, `OAI.UniversalTensorSquare.sg35458`, `OAI.UniversalTensorSquare.sg35460`, `OAI.UniversalTensorSquare.sg35462`, `OAI.UniversalTensorSquare.sg35465`, `OAI.UniversalTensorSquare.sg35466`, `OAI.UniversalTensorSquare.sg35467`, `OAI.UniversalTensorSquare.sg35469`, `OAI.UniversalTensorSquare.sg35481`, `OAI.UniversalTensorSquare.sg35501`, `OAI.UniversalTensorSquare.sg35507`, `OAI.UniversalTensorSquare.sg35508`, `OAI.UniversalTensorSquare.sg35509`, `OAI.UniversalTensorSquare.sg35585`, `OAI.UniversalTensorSquare.sg35589`, `OAI.UniversalTensorSquare.sg35597`, `OAI.UniversalTensorSquare.sg35599`, `OAI.UniversalTensorSquare.sg35601`, `OAI.UniversalTensorSquare.sg35610`, `OAI.UniversalTensorSquare.sg35632`, `OAI.UniversalTensorSquare.sg35634`, `OAI.UniversalTensorSquare.sg35635`, `OAI.UniversalTensorSquare.sg35644`, `OAI.UniversalTensorSquare.sg35766`, `OAI.UniversalTensorSquare.sg35786`, `OAI.UniversalTensorSquare.sg35801`, `OAI.UniversalTensorSquare.sg35808`, `OAI.UniversalTensorSquare.sg35811`, `OAI.UniversalTensorSquare.sg35813`, `OAI.UniversalTensorSquare.sg35835`, `OAI.UniversalTensorSquare.sg35836`, `OAI.UniversalTensorSquare.sg35933`, `OAI.UniversalTensorSquare.sg35972`, `OAI.UniversalTensorSquare.sg35983`, `OAI.UniversalTensorSquare.sg36088`, `OAI.UniversalTensorSquare.sg36099`, `OAI.UniversalTensorSquare.sg36103`, `OAI.UniversalTensorSquare.sg36116`, `OAI.UniversalTensorSquare.sg36122`, `OAI.UniversalTensorSquare.sg36124`, `OAI.UniversalTensorSquare.sg36126`, `OAI.UniversalTensorSquare.sg36127`, `OAI.UniversalTensorSquare.sg36145`, `OAI.UniversalTensorSquare.sg36146`, `OAI.UniversalTensorSquare.sg36174`, `OAI.UniversalTensorSquare.sg36176`, `OAI.UniversalTensorSquare.sg36178`, `OAI.UniversalTensorSquare.sg36181`, `OAI.UniversalTensorSquare.sg36209`, `OAI.UniversalTensorSquare.sg36210`, `OAI.UniversalTensorSquare.sg36218`, `OAI.UniversalTensorSquare.sg36220`, `OAI.UniversalTensorSquare.sg36281`, `OAI.UniversalTensorSquare.sg36286`, `OAI.UniversalTensorSquare.sg36287`, `OAI.UniversalTensorSquare.sg36289`, `OAI.UniversalTensorSquare.sg36290`, `OAI.UniversalTensorSquare.sg36292`, `OAI.UniversalTensorSquare.sg36293`, `OAI.UniversalTensorSquare.sg36294`, `OAI.UniversalTensorSquare.sg36296`, `OAI.UniversalTensorSquare.sg36297`, `OAI.UniversalTensorSquare.sg36300`, `OAI.UniversalTensorSquare.sg36303`, `OAI.UniversalTensorSquare.sg36318`, `OAI.UniversalTensorSquare.sg36340`, `OAI.UniversalTensorSquare.sg36400`, `OAI.UniversalTensorSquare.sg36406`, `OAI.UniversalTensorSquare.sg36449`, `OAI.UniversalTensorSquare.sg36452`, `OAI.UniversalTensorSquare.sg36454`, `OAI.UniversalTensorSquare.sg36461`, `OAI.UniversalTensorSquare.sg36463`, `OAI.UniversalTensorSquare.sg36468`, `OAI.UniversalTensorSquare.sg36519`, `OAI.UniversalTensorSquare.sg36525`, `OAI.UniversalTensorSquare.sg36529`, `OAI.UniversalTensorSquare.sg36534`, `OAI.UniversalTensorSquare.sg36535`, `OAI.UniversalTensorSquare.sg36537`, `OAI.UniversalTensorSquare.sg36540`, `OAI.UniversalTensorSquare.sg36544`, `OAI.UniversalTensorSquare.sg36566`, `OAI.UniversalTensorSquare.sg36584`, `OAI.UniversalTensorSquare.sg36588`, `OAI.UniversalTensorSquare.sg36590`, `OAI.UniversalTensorSquare.sg36592`, `OAI.UniversalTensorSquare.sg36612`, `OAI.UniversalTensorSquare.sg36620`, `OAI.UniversalTensorSquare.sg36667`, `OAI.UniversalTensorSquare.sg36704`, `OAI.UniversalTensorSquare.sg36723`, `OAI.UniversalTensorSquare.sg36773`, `OAI.UniversalTensorSquare.sg36775`, `OAI.UniversalTensorSquare.sg36779`, `OAI.UniversalTensorSquare.sg36782`, `OAI.UniversalTensorSquare.sg36784`, `OAI.UniversalTensorSquare.sg36801`, `OAI.UniversalTensorSquare.sg36804`, `OAI.UniversalTensorSquare.sg36811`, `OAI.UniversalTensorSquare.sg36814`, `OAI.UniversalTensorSquare.sg36839`, `OAI.UniversalTensorSquare.sg36864`, `OAI.UniversalTensorSquare.sg36867`, `OAI.UniversalTensorSquare.sg36869`, `OAI.UniversalTensorSquare.sg36877`, `OAI.UniversalTensorSquare.sg36886`, `OAI.UniversalTensorSquare.sg36889`, `OAI.UniversalTensorSquare.sg36891`, `OAI.UniversalTensorSquare.sg36921`, `OAI.UniversalTensorSquare.sg36980`, `OAI.UniversalTensorSquare.sg36981`, `OAI.UniversalTensorSquare.sg36993`, `OAI.UniversalTensorSquare.sg36995`, `OAI.UniversalTensorSquare.sg37019`, `OAI.UniversalTensorSquare.sg37020`, `OAI.UniversalTensorSquare.sg37023`, `OAI.UniversalTensorSquare.sg37027`, `OAI.UniversalTensorSquare.sg37029`, `OAI.UniversalTensorSquare.sg37031`, `OAI.UniversalTensorSquare.sg37033`, `OAI.UniversalTensorSquare.sg37034`, `OAI.UniversalTensorSquare.sg37040`, `OAI.UniversalTensorSquare.sg37041`, `OAI.UniversalTensorSquare.sg37042`, `OAI.UniversalTensorSquare.sg37044`, `OAI.UniversalTensorSquare.sg37051`, `OAI.UniversalTensorSquare.sg37053`, `OAI.UniversalTensorSquare.sg37055`, `OAI.UniversalTensorSquare.sg37057`, `OAI.UniversalTensorSquare.sg37093`, `OAI.UniversalTensorSquare.sg37258`, `OAI.UniversalTensorSquare.sg37261`, `OAI.UniversalTensorSquare.sg37263`, `OAI.UniversalTensorSquare.sg37280`, `OAI.UniversalTensorSquare.sg37289`, `OAI.UniversalTensorSquare.sg37311`, `OAI.UniversalTensorSquare.sg37325`, `OAI.UniversalTensorSquare.sg37331`, `OAI.UniversalTensorSquare.sg37400`, `OAI.UniversalTensorSquare.sg37402`, `OAI.UniversalTensorSquare.sg37414`, `OAI.UniversalTensorSquare.sg37421`, `OAI.UniversalTensorSquare.sg37424`, `OAI.UniversalTensorSquare.sg37426`, `OAI.UniversalTensorSquare.sg37436`, `OAI.UniversalTensorSquare.sg37441`, `OAI.UniversalTensorSquare.sg37443`, `OAI.UniversalTensorSquare.sg37471`, `OAI.UniversalTensorSquare.sg37474`, `OAI.UniversalTensorSquare.sg37476`, `OAI.UniversalTensorSquare.sg37484`, `OAI.UniversalTensorSquare.sg37486`, `OAI.UniversalTensorSquare.sg37549`, `OAI.UniversalTensorSquare.sg37552`, `OAI.UniversalTensorSquare.sg37555`, `OAI.UniversalTensorSquare.sg37559`, `OAI.UniversalTensorSquare.sg37561`, `OAI.UniversalTensorSquare.sg37578`, `OAI.UniversalTensorSquare.sg37581`, `OAI.UniversalTensorSquare.sg37583`, `OAI.UniversalTensorSquare.sg37588`, `OAI.UniversalTensorSquare.sg37590`, `OAI.UniversalTensorSquare.sg37600`, `OAI.UniversalTensorSquare.sg37608`, `OAI.UniversalTensorSquare.sg37620`, `OAI.UniversalTensorSquare.sg37621`, `OAI.UniversalTensorSquare.sg37622`, `OAI.UniversalTensorSquare.sg37624`, `OAI.UniversalTensorSquare.sg37625`, `OAI.UniversalTensorSquare.sg37627`, `OAI.UniversalTensorSquare.sg37628`, `OAI.UniversalTensorSquare.sg37630`, `OAI.UniversalTensorSquare.sg37635`, `OAI.UniversalTensorSquare.sg37637`, `OAI.UniversalTensorSquare.sg37643`, `OAI.UniversalTensorSquare.sg37664`, `OAI.UniversalTensorSquare.sg37669`, `OAI.UniversalTensorSquare.sg37671`, `OAI.UniversalTensorSquare.sg37673`, `OAI.UniversalTensorSquare.sg37702`, `OAI.UniversalTensorSquare.sg37704`, `OAI.UniversalTensorSquare.sg37821`, `OAI.UniversalTensorSquare.sg37822`, `OAI.UniversalTensorSquare.sg37824`, `OAI.UniversalTensorSquare.sg37826`, `OAI.UniversalTensorSquare.sg37860`, `OAI.UniversalTensorSquare.sg37909`, `OAI.UniversalTensorSquare.sg37914`, `OAI.UniversalTensorSquare.sg37917`, `OAI.UniversalTensorSquare.sg37919`, `OAI.UniversalTensorSquare.sg37946`, `OAI.UniversalTensorSquare.sg37958`, `OAI.UniversalTensorSquare.sg38024`, `OAI.UniversalTensorSquare.sg38044`, `OAI.UniversalTensorSquare.sg38048`, `OAI.UniversalTensorSquare.sg38065`, `OAI.UniversalTensorSquare.sg38092`, `OAI.UniversalTensorSquare.sg38095`, `OAI.UniversalTensorSquare.sg38097`, `OAI.UniversalTensorSquare.sg38118`, `OAI.UniversalTensorSquare.sg38119`, `OAI.UniversalTensorSquare.sg38120`, `OAI.UniversalTensorSquare.sg38122`, `OAI.UniversalTensorSquare.sg38123`, `OAI.UniversalTensorSquare.sg38125`, `OAI.UniversalTensorSquare.sg38126`, `OAI.UniversalTensorSquare.sg38130`, `OAI.UniversalTensorSquare.sg38132`, `OAI.UniversalTensorSquare.sg38149`, `OAI.UniversalTensorSquare.sg38152`, `OAI.UniversalTensorSquare.sg38154`, `OAI.UniversalTensorSquare.sg38172`, `OAI.UniversalTensorSquare.sg38174`, `OAI.UniversalTensorSquare.sg38177`, `OAI.UniversalTensorSquare.sg38183`, `OAI.UniversalTensorSquare.sg38184`, `OAI.UniversalTensorSquare.sg38193`, `OAI.UniversalTensorSquare.sg38228`, `OAI.UniversalTensorSquare.sg38267`, `OAI.UniversalTensorSquare.sg38279`, `OAI.UniversalTensorSquare.sg38293`, `OAI.UniversalTensorSquare.sg38298`, `OAI.UniversalTensorSquare.sg38301`, `OAI.UniversalTensorSquare.sg38303`, `OAI.UniversalTensorSquare.sg38308`, `OAI.UniversalTensorSquare.sg38317`, `OAI.UniversalTensorSquare.sg38341`, `OAI.UniversalTensorSquare.sg38342`, `OAI.UniversalTensorSquare.sg38345`, `OAI.UniversalTensorSquare.sg38346`, `OAI.UniversalTensorSquare.sg38348`, `OAI.UniversalTensorSquare.sg38349`, `OAI.UniversalTensorSquare.sg38356`, `OAI.UniversalTensorSquare.sg38360`, `OAI.UniversalTensorSquare.sg38361`, `OAI.UniversalTensorSquare.sg38363`, `OAI.UniversalTensorSquare.sg38364`, `OAI.UniversalTensorSquare.sg38366`, `OAI.UniversalTensorSquare.sg38368`, `OAI.UniversalTensorSquare.sg38392`, `OAI.UniversalTensorSquare.sg38395`, `OAI.UniversalTensorSquare.sg38397`, `OAI.UniversalTensorSquare.sg38405`, `OAI.UniversalTensorSquare.sg38413`, `OAI.UniversalTensorSquare.sg38416`, `OAI.UniversalTensorSquare.sg38418`, `OAI.UniversalTensorSquare.sg38477`, `OAI.UniversalTensorSquare.sg38485`, `OAI.UniversalTensorSquare.sg38488`, `OAI.UniversalTensorSquare.sg38518`, `OAI.UniversalTensorSquare.sg38521`, `OAI.UniversalTensorSquare.sg38523`, `OAI.UniversalTensorSquare.sg38550`, `OAI.UniversalTensorSquare.sg38591`, `OAI.UniversalTensorSquare.sg38593`, `OAI.UniversalTensorSquare.sg38612`, `OAI.UniversalTensorSquare.sg38617`, `OAI.UniversalTensorSquare.sg38661`, `OAI.UniversalTensorSquare.sg38686`, `OAI.UniversalTensorSquare.sg38688`, `OAI.UniversalTensorSquare.sg38696`, `OAI.UniversalTensorSquare.sg38707`, `OAI.UniversalTensorSquare.sg38710`, `OAI.UniversalTensorSquare.sg38712`, `OAI.UniversalTensorSquare.sg38721`, `OAI.UniversalTensorSquare.sg38727`, `OAI.UniversalTensorSquare.sg38749`, `OAI.UniversalTensorSquare.sg38752`, `OAI.UniversalTensorSquare.sg38754`, `OAI.UniversalTensorSquare.sg38758`, `OAI.UniversalTensorSquare.sg38759`, `OAI.UniversalTensorSquare.sg38762`, `OAI.UniversalTensorSquare.sg38808`, `OAI.UniversalTensorSquare.sg38847`, `OAI.UniversalTensorSquare.sg38849`, `OAI.UniversalTensorSquare.sg38856`, `OAI.UniversalTensorSquare.sg38871`, `OAI.UniversalTensorSquare.sg38873`, `OAI.UniversalTensorSquare.sg38879`, `OAI.UniversalTensorSquare.sg38898`, `OAI.UniversalTensorSquare.sg38902`, `OAI.UniversalTensorSquare.sg38911`, `OAI.UniversalTensorSquare.sg38918`, `OAI.UniversalTensorSquare.sg38919`, `OAI.UniversalTensorSquare.sg38952`, `OAI.UniversalTensorSquare.sg38967`, `OAI.UniversalTensorSquare.sg38970`, `OAI.UniversalTensorSquare.sg38972`, `OAI.UniversalTensorSquare.sg39024`, `OAI.UniversalTensorSquare.sg39027`, `OAI.UniversalTensorSquare.sg39029`, `OAI.UniversalTensorSquare.sg39042`, `OAI.UniversalTensorSquare.sg39044`, `OAI.UniversalTensorSquare.sg39046`, `OAI.UniversalTensorSquare.sg39052`, `OAI.UniversalTensorSquare.sg39059`, `OAI.UniversalTensorSquare.sg39061`, `OAI.UniversalTensorSquare.sg39063`, `OAI.UniversalTensorSquare.sg39070`, `OAI.UniversalTensorSquare.sg39072`, `OAI.UniversalTensorSquare.sg39083`, `OAI.UniversalTensorSquare.sg39086`, `OAI.UniversalTensorSquare.sg39088`, `OAI.UniversalTensorSquare.sg39107`, `OAI.UniversalTensorSquare.sg39110`, `OAI.UniversalTensorSquare.sg39112`, `OAI.UniversalTensorSquare.sg39119`, `OAI.UniversalTensorSquare.sg39143`, `OAI.UniversalTensorSquare.sg39144`, `OAI.UniversalTensorSquare.sg39147`, `OAI.UniversalTensorSquare.sg39174`, `OAI.UniversalTensorSquare.sg39210`, `OAI.UniversalTensorSquare.sg39213`, `OAI.UniversalTensorSquare.sg39215`, `OAI.UniversalTensorSquare.sg39237`, `OAI.UniversalTensorSquare.sg39239`, `OAI.UniversalTensorSquare.sg39241`, `OAI.UniversalTensorSquare.sg39274`, `OAI.UniversalTensorSquare.sg39277`, `OAI.UniversalTensorSquare.sg39282`, `OAI.UniversalTensorSquare.sg39285`, `OAI.UniversalTensorSquare.sg39289`, `OAI.UniversalTensorSquare.sg39304`, `OAI.UniversalTensorSquare.sg39307`, `OAI.UniversalTensorSquare.sg39308`, `OAI.UniversalTensorSquare.sg39314`, `OAI.UniversalTensorSquare.sg39317`, `OAI.UniversalTensorSquare.sg39318`, `OAI.UniversalTensorSquare.sg39321`, `OAI.UniversalTensorSquare.sg39332`, `OAI.UniversalTensorSquare.sg39345`, `OAI.UniversalTensorSquare.sg39347`, `OAI.UniversalTensorSquare.sg39351`, `OAI.UniversalTensorSquare.sg39354`, `OAI.UniversalTensorSquare.sg39355`, `OAI.UniversalTensorSquare.sg39382`, `OAI.UniversalTensorSquare.sg39390`, `OAI.UniversalTensorSquare.sg39395`, `OAI.UniversalTensorSquare.sg39397`, `OAI.UniversalTensorSquare.sg39413`, `OAI.UniversalTensorSquare.sg39421`, `OAI.UniversalTensorSquare.sg39422`, `OAI.UniversalTensorSquare.sg39437`, `OAI.UniversalTensorSquare.sg39442`, `OAI.UniversalTensorSquare.sg39445`, `OAI.UniversalTensorSquare.sg39446`, `OAI.UniversalTensorSquare.sg39457`, `OAI.UniversalTensorSquare.sg39471`, `OAI.UniversalTensorSquare.sg39477`, `OAI.UniversalTensorSquare.sg39480`, `OAI.UniversalTensorSquare.sg39481`, `OAI.UniversalTensorSquare.sg39483`, `OAI.UniversalTensorSquare.sg39487`, `OAI.UniversalTensorSquare.sg39493`, `OAI.UniversalTensorSquare.sg39494`, `OAI.UniversalTensorSquare.sg39511`, `OAI.UniversalTensorSquare.sg39515`, `OAI.UniversalTensorSquare.sg39518`, `OAI.UniversalTensorSquare.sg39519`, `OAI.UniversalTensorSquare.sg39548`, `OAI.UniversalTensorSquare.sg39551`, `OAI.UniversalTensorSquare.sg39552`, `OAI.UniversalTensorSquare.sg39578`, `OAI.UniversalTensorSquare.sg39580`, `OAI.UniversalTensorSquare.sg39581`, `OAI.UniversalTensorSquare.sg39587`, `OAI.UniversalTensorSquare.sg39661`, `OAI.UniversalTensorSquare.sg39664`, `OAI.UniversalTensorSquare.sg39665`, `OAI.UniversalTensorSquare.sg39755`, `OAI.UniversalTensorSquare.sg39776`, `OAI.UniversalTensorSquare.sg39779`, `OAI.UniversalTensorSquare.sg39838`, `OAI.UniversalTensorSquare.sg39862`, `OAI.UniversalTensorSquare.sg39880`, `OAI.UniversalTensorSquare.sg39886`, `OAI.UniversalTensorSquare.sg39887`, `OAI.UniversalTensorSquare.sg39888`, `OAI.UniversalTensorSquare.sg39890`, `OAI.UniversalTensorSquare.sg39891`, `OAI.UniversalTensorSquare.sg39892`, `OAI.UniversalTensorSquare.sg39895`, `OAI.UniversalTensorSquare.sg39902`, `OAI.UniversalTensorSquare.sg39903`, `OAI.UniversalTensorSquare.sg39905`, `OAI.UniversalTensorSquare.sg39907`, `OAI.UniversalTensorSquare.sg39909`, `OAI.UniversalTensorSquare.sg39913`, `OAI.UniversalTensorSquare.sg39919`, `OAI.UniversalTensorSquare.sg39936`, `OAI.UniversalTensorSquare.sg39937`, `OAI.UniversalTensorSquare.sg39942`, `OAI.UniversalTensorSquare.sg39954`, `OAI.UniversalTensorSquare.sg39959`, `OAI.UniversalTensorSquare.sg39970`, `OAI.UniversalTensorSquare.sg39971`, `OAI.UniversalTensorSquare.sg39972`, `OAI.UniversalTensorSquare.sg39981`, `OAI.UniversalTensorSquare.sg39983`, `OAI.UniversalTensorSquare.sg39984`, `OAI.UniversalTensorSquare.sg40021`, `OAI.UniversalTensorSquare.sg40027`, `OAI.UniversalTensorSquare.sg40029`, `OAI.UniversalTensorSquare.sg40030`, `OAI.UniversalTensorSquare.sg40039`, `OAI.UniversalTensorSquare.sg40046`, `OAI.UniversalTensorSquare.sg40049`, `OAI.UniversalTensorSquare.sg40061`, `OAI.UniversalTensorSquare.sg40063`, `OAI.UniversalTensorSquare.sg40064`, `OAI.UniversalTensorSquare.sg40076`, `OAI.UniversalTensorSquare.sg40078`, `OAI.UniversalTensorSquare.sg40079`, `OAI.UniversalTensorSquare.sg40097`, `OAI.UniversalTensorSquare.sg40099`, `OAI.UniversalTensorSquare.sg40100`, `OAI.UniversalTensorSquare.sg40127`, `OAI.UniversalTensorSquare.sg40131`, `OAI.UniversalTensorSquare.sg40133`, `OAI.UniversalTensorSquare.sg40134`, `OAI.UniversalTensorSquare.sg40136`, `OAI.UniversalTensorSquare.sg40138`, `OAI.UniversalTensorSquare.sg40165`, `OAI.UniversalTensorSquare.sg40167`, `OAI.UniversalTensorSquare.sg40168`, `OAI.UniversalTensorSquare.sg40170`, `OAI.UniversalTensorSquare.sg40174`, `OAI.UniversalTensorSquare.sg40177`, `OAI.UniversalTensorSquare.sg40180`, `OAI.UniversalTensorSquare.sg40181`, `OAI.UniversalTensorSquare.sg40183`, `OAI.UniversalTensorSquare.sg40197`, `OAI.UniversalTensorSquare.sg40198`, `OAI.UniversalTensorSquare.sg40199`, `OAI.UniversalTensorSquare.sg40200`, `OAI.UniversalTensorSquare.sg40201`, `OAI.UniversalTensorSquare.sg40202`, `OAI.UniversalTensorSquare.sg40205`, `OAI.UniversalTensorSquare.sg40221`, `OAI.UniversalTensorSquare.sg40241`, `OAI.UniversalTensorSquare.sg40244`, `OAI.UniversalTensorSquare.sg40245`, `OAI.UniversalTensorSquare.sg40256`, `OAI.UniversalTensorSquare.sg40313`, `OAI.UniversalTensorSquare.sg40356`, `OAI.UniversalTensorSquare.sg40357`, `OAI.UniversalTensorSquare.sg40381`, `OAI.UniversalTensorSquare.sg40422`, `OAI.UniversalTensorSquare.sg40450`, `OAI.UniversalTensorSquare.sg40482`, `OAI.UniversalTensorSquare.sg40484`, `OAI.UniversalTensorSquare.sg40485`, `OAI.UniversalTensorSquare.sg40517`, `OAI.UniversalTensorSquare.sg40521`, `OAI.UniversalTensorSquare.sg40553`, `OAI.UniversalTensorSquare.sg40571`, `OAI.UniversalTensorSquare.sg40582`, `OAI.UniversalTensorSquare.sg40613`, `OAI.UniversalTensorSquare.sg40614`, `OAI.UniversalTensorSquare.sg40616`, `OAI.UniversalTensorSquare.sg40619`, `OAI.UniversalTensorSquare.sg40622`, `OAI.UniversalTensorSquare.sg40623`, `OAI.UniversalTensorSquare.sg40630`, `OAI.UniversalTensorSquare.sg40631`, `OAI.UniversalTensorSquare.sg40632`, `OAI.UniversalTensorSquare.sg40633`, `OAI.UniversalTensorSquare.sg40634`, `OAI.UniversalTensorSquare.sg40657`, `OAI.UniversalTensorSquare.sg40659`, `OAI.UniversalTensorSquare.sg40660`, `OAI.UniversalTensorSquare.sg40664`, `OAI.UniversalTensorSquare.sg40666`, `OAI.UniversalTensorSquare.sg40667`, `OAI.UniversalTensorSquare.sg40676`, `OAI.UniversalTensorSquare.sg40678`, `OAI.UniversalTensorSquare.sg40679`, `OAI.UniversalTensorSquare.sg40681`, `OAI.UniversalTensorSquare.sg40682`, `OAI.UniversalTensorSquare.sg40710`, `OAI.UniversalTensorSquare.sg40713`, `OAI.UniversalTensorSquare.sg40714`, `OAI.UniversalTensorSquare.sg40716`, `OAI.UniversalTensorSquare.sg40724`, `OAI.UniversalTensorSquare.sg40726`, `OAI.UniversalTensorSquare.sg40727`, `OAI.UniversalTensorSquare.sg40738`, `OAI.UniversalTensorSquare.sg40748`, `OAI.UniversalTensorSquare.sg40751`, `OAI.UniversalTensorSquare.sg40754`, `OAI.UniversalTensorSquare.sg40758`, `OAI.UniversalTensorSquare.sg40760`, `OAI.UniversalTensorSquare.sg40761`, `OAI.UniversalTensorSquare.sg40763`, `OAI.UniversalTensorSquare.sg40769`, `OAI.UniversalTensorSquare.sg40770`, `OAI.UniversalTensorSquare.sg40791`, `OAI.UniversalTensorSquare.sg40794`, `OAI.UniversalTensorSquare.sg40795`, `OAI.UniversalTensorSquare.sg40808`, `OAI.UniversalTensorSquare.sg40812`, `OAI.UniversalTensorSquare.sg40814`, `OAI.UniversalTensorSquare.sg40815`, `OAI.UniversalTensorSquare.sg40841`, `OAI.UniversalTensorSquare.sg40879`, `OAI.UniversalTensorSquare.sg40897`, `OAI.UniversalTensorSquare.sg40898`, `OAI.UniversalTensorSquare.sg40899`, `OAI.UniversalTensorSquare.sg40908`, `OAI.UniversalTensorSquare.sg40910`, `OAI.UniversalTensorSquare.sg40911`, `OAI.UniversalTensorSquare.sg40916`, `OAI.UniversalTensorSquare.sg40917`, `OAI.UniversalTensorSquare.sg40918`, `OAI.UniversalTensorSquare.sg40942`, `OAI.UniversalTensorSquare.sg40959`, `OAI.UniversalTensorSquare.sg40985`, `OAI.UniversalTensorSquare.sg40986`, `OAI.UniversalTensorSquare.sg40999`, `OAI.UniversalTensorSquare.sg41005`, `OAI.UniversalTensorSquare.sg41007`, `OAI.UniversalTensorSquare.sg41021`, `OAI.UniversalTensorSquare.sg41024`, `OAI.UniversalTensorSquare.sg41025`, `OAI.UniversalTensorSquare.sg41026`, `OAI.UniversalTensorSquare.sg41031`, `OAI.UniversalTensorSquare.sg41032`, `OAI.UniversalTensorSquare.sg41034`, `OAI.UniversalTensorSquare.sg41052`, `OAI.UniversalTensorSquare.sg41054`, `OAI.UniversalTensorSquare.sg41055`, `OAI.UniversalTensorSquare.sg41059`, `OAI.UniversalTensorSquare.sg41060`, `OAI.UniversalTensorSquare.sg41062`, `OAI.UniversalTensorSquare.sg41068`, `OAI.UniversalTensorSquare.sg41077`, `OAI.UniversalTensorSquare.sg41078`, `OAI.UniversalTensorSquare.sg41094`, `OAI.UniversalTensorSquare.sg41095`, `OAI.UniversalTensorSquare.sg41105`, `OAI.UniversalTensorSquare.sg41106`, `OAI.UniversalTensorSquare.sg41114`, `OAI.UniversalTensorSquare.sg41116`, `OAI.UniversalTensorSquare.sg41130`, `OAI.UniversalTensorSquare.sg41139`, `OAI.UniversalTensorSquare.sg41141`, `OAI.UniversalTensorSquare.sg41142`, `OAI.UniversalTensorSquare.sg41143`, `OAI.UniversalTensorSquare.sg41144`, `OAI.UniversalTensorSquare.sg41145`, `OAI.UniversalTensorSquare.sg41146`, `OAI.UniversalTensorSquare.sg41154`, `OAI.UniversalTensorSquare.sg41155`, `OAI.UniversalTensorSquare.sg41168`, `OAI.UniversalTensorSquare.sg41170`, `OAI.UniversalTensorSquare.sg41171`, `OAI.UniversalTensorSquare.sg41177`, `OAI.UniversalTensorSquare.sg41178`, `OAI.UniversalTensorSquare.sg41179`, `OAI.UniversalTensorSquare.sg41180`, `OAI.UniversalTensorSquare.sg41195`, `OAI.UniversalTensorSquare.sg41197`, `OAI.UniversalTensorSquare.sg41203`, `OAI.UniversalTensorSquare.sg41209`, `OAI.UniversalTensorSquare.sg41211`, `OAI.UniversalTensorSquare.sg41212`, `OAI.UniversalTensorSquare.sg41224`, `OAI.UniversalTensorSquare.sg41245`, `OAI.UniversalTensorSquare.sg41256`, `OAI.UniversalTensorSquare.sg41267`, `OAI.UniversalTensorSquare.sg41277`, `OAI.UniversalTensorSquare.sg41278`, `OAI.UniversalTensorSquare.sg41280`, `OAI.UniversalTensorSquare.sg41301`, `OAI.UniversalTensorSquare.sg41302`, `OAI.UniversalTensorSquare.sg41336`, `OAI.UniversalTensorSquare.sg41346`, `OAI.UniversalTensorSquare.sg41347`, `OAI.UniversalTensorSquare.sg41359`, `OAI.UniversalTensorSquare.sg41363`, `OAI.UniversalTensorSquare.sg41375`, `OAI.UniversalTensorSquare.sg41385`, `OAI.UniversalTensorSquare.sg41386`, `OAI.UniversalTensorSquare.sg41388`, `OAI.UniversalTensorSquare.sg41394`, `OAI.UniversalTensorSquare.sg41397`, `OAI.UniversalTensorSquare.sg41409`, `OAI.UniversalTensorSquare.sg41413`, `OAI.UniversalTensorSquare.sg41439`, `OAI.UniversalTensorSquare.sg41440`, `OAI.UniversalTensorSquare.sg41442`, `OAI.UniversalTensorSquare.sg41451`, `OAI.UniversalTensorSquare.sg41457`, `OAI.UniversalTensorSquare.sg41460`, `OAI.UniversalTensorSquare.sg41466`, `OAI.UniversalTensorSquare.sg41480`, `OAI.UniversalTensorSquare.sg41482`, `OAI.UniversalTensorSquare.sg41490`, `OAI.UniversalTensorSquare.sg41492`, `OAI.UniversalTensorSquare.sg41496`, `OAI.UniversalTensorSquare.sg41503`, `OAI.UniversalTensorSquare.sg41524`, `OAI.UniversalTensorSquare.sg41533`, `OAI.UniversalTensorSquare.sg41535`, `OAI.UniversalTensorSquare.sg41552`, `OAI.UniversalTensorSquare.sg41560`, `OAI.UniversalTensorSquare.sg41574`, `OAI.UniversalTensorSquare.sg41575`, `OAI.UniversalTensorSquare.sg41601`, `OAI.UniversalTensorSquare.sg41625`, `OAI.UniversalTensorSquare.sg41627`, `OAI.UniversalTensorSquare.sg41641`, `OAI.UniversalTensorSquare.sg41645`, `OAI.UniversalTensorSquare.sg41662`, `OAI.UniversalTensorSquare.sg41680`, `OAI.UniversalTensorSquare.sg41714`, `OAI.UniversalTensorSquare.sg41717`, `OAI.UniversalTensorSquare.sg41718`, `OAI.UniversalTensorSquare.sg41720`, `OAI.UniversalTensorSquare.sg41725`, `OAI.UniversalTensorSquare.sg41729`, `OAI.UniversalTensorSquare.sg41755`, `OAI.UniversalTensorSquare.sg41769`, `OAI.UniversalTensorSquare.sg41775`, `OAI.UniversalTensorSquare.sg41794`, `OAI.UniversalTensorSquare.sg41807`, `OAI.UniversalTensorSquare.sg41808`, `OAI.UniversalTensorSquare.sg41816`, `OAI.UniversalTensorSquare.sg41817`, `OAI.UniversalTensorSquare.sg41819`, `OAI.UniversalTensorSquare.sg41823`, `OAI.UniversalTensorSquare.sg41824`, `OAI.UniversalTensorSquare.sg41826`, `OAI.UniversalTensorSquare.sg41834`, `OAI.UniversalTensorSquare.sg41838`, `OAI.UniversalTensorSquare.sg41859`, `OAI.UniversalTensorSquare.sg41868`, `OAI.UniversalTensorSquare.sg41900`, `OAI.UniversalTensorSquare.sg41932`, `OAI.UniversalTensorSquare.sg41940`, `OAI.UniversalTensorSquare.sg41968`, `OAI.UniversalTensorSquare.sg41983`, `OAI.UniversalTensorSquare.sg42015`, `OAI.UniversalTensorSquare.sg42026`, `OAI.UniversalTensorSquare.sg42056`, `OAI.UniversalTensorSquare.sg42059`, `OAI.UniversalTensorSquare.sg42066`, `OAI.UniversalTensorSquare.sg42068`, `OAI.UniversalTensorSquare.sg42076`, `OAI.UniversalTensorSquare.sg42106`, `OAI.UniversalTensorSquare.sg42127`, `OAI.UniversalTensorSquare.sg42132`, `OAI.UniversalTensorSquare.sg42167`, `OAI.UniversalTensorSquare.sg42172`, `OAI.UniversalTensorSquare.sg42173`, `OAI.UniversalTensorSquare.sg42174`, `OAI.UniversalTensorSquare.sg42197`, `OAI.UniversalTensorSquare.sg42216`, `OAI.UniversalTensorSquare.sg42272`, `OAI.UniversalTensorSquare.sg42281`, `OAI.UniversalTensorSquare.sg42282`, `OAI.UniversalTensorSquare.sg42326`, `OAI.UniversalTensorSquare.sg42336`, `OAI.UniversalTensorSquare.sg42337`, `OAI.UniversalTensorSquare.sg42339`, `OAI.UniversalTensorSquare.sg42347`, `OAI.UniversalTensorSquare.sg42349`, `OAI.UniversalTensorSquare.sg42360`, `OAI.UniversalTensorSquare.sg42371`, `OAI.UniversalTensorSquare.sg42375`, `OAI.UniversalTensorSquare.sg42484`, `OAI.UniversalTensorSquare.sg42490`, `OAI.UniversalTensorSquare.sg42513`, `OAI.UniversalTensorSquare.sg42522`, `OAI.UniversalTensorSquare.sg42524`, `OAI.UniversalTensorSquare.sg42528`, `OAI.UniversalTensorSquare.sg42535`, `OAI.UniversalTensorSquare.sg42562`, `OAI.UniversalTensorSquare.sg42612`, `OAI.UniversalTensorSquare.sg42621`, `OAI.UniversalTensorSquare.sg42625`, `OAI.UniversalTensorSquare.sg42628`, `OAI.UniversalTensorSquare.sg42637`, `OAI.UniversalTensorSquare.sg42651`, `OAI.UniversalTensorSquare.sg42662`, `OAI.UniversalTensorSquare.sg42663`, `OAI.UniversalTensorSquare.sg42667`, `OAI.UniversalTensorSquare.sg42670`, `OAI.UniversalTensorSquare.sg42671`, `OAI.UniversalTensorSquare.sg42675`, `OAI.UniversalTensorSquare.sg42678`, `OAI.UniversalTensorSquare.sg42687`, `OAI.UniversalTensorSquare.sg42691`, `OAI.UniversalTensorSquare.sg42720`, `OAI.UniversalTensorSquare.sg42740`, `OAI.UniversalTensorSquare.sg42747`, `OAI.UniversalTensorSquare.sg42750`, `OAI.UniversalTensorSquare.sg42751`, `OAI.UniversalTensorSquare.sg42755`, `OAI.UniversalTensorSquare.sg42763`, `OAI.UniversalTensorSquare.sg42765`, `OAI.UniversalTensorSquare.sg42775`, `OAI.UniversalTensorSquare.sg42792`, `OAI.UniversalTensorSquare.sg42809`, `OAI.UniversalTensorSquare.sg42810`, `OAI.UniversalTensorSquare.sg42824`, `OAI.UniversalTensorSquare.sg42825`, `OAI.UniversalTensorSquare.sg42829`, `OAI.UniversalTensorSquare.sg42833`, `OAI.UniversalTensorSquare.sg42834`, `OAI.UniversalTensorSquare.sg42838`, `OAI.UniversalTensorSquare.sg42839`, `OAI.UniversalTensorSquare.sg42842`, `OAI.UniversalTensorSquare.sg42861`, `OAI.UniversalTensorSquare.sg42863`, `OAI.UniversalTensorSquare.sg42875`, `OAI.UniversalTensorSquare.sg42880`, `OAI.UniversalTensorSquare.sg42881`, `OAI.UniversalTensorSquare.sg42889`, `OAI.UniversalTensorSquare.sg42895`, `OAI.UniversalTensorSquare.sg42900`, `OAI.UniversalTensorSquare.sg42901`, `OAI.UniversalTensorSquare.sg42911`, `OAI.UniversalTensorSquare.sg42912`, `OAI.UniversalTensorSquare.sg42915`, `OAI.UniversalTensorSquare.sg42938`, `OAI.UniversalTensorSquare.sg42939`, `OAI.UniversalTensorSquare.sg42953`, `OAI.UniversalTensorSquare.sg42954`, `OAI.UniversalTensorSquare.sg42961`, `OAI.UniversalTensorSquare.sg42962`, `OAI.UniversalTensorSquare.sg42970`, `OAI.UniversalTensorSquare.sg42973`, `OAI.UniversalTensorSquare.sg42974`, `OAI.UniversalTensorSquare.sg42983`, `OAI.UniversalTensorSquare.sg42989`, `OAI.UniversalTensorSquare.sg42990`, `OAI.UniversalTensorSquare.sg42995`, `OAI.UniversalTensorSquare.sg42996`, `OAI.UniversalTensorSquare.sg43003`, `OAI.UniversalTensorSquare.sg43016`, `OAI.UniversalTensorSquare.sg43020`, `OAI.UniversalTensorSquare.sg43024`, `OAI.UniversalTensorSquare.sg43027`, `OAI.UniversalTensorSquare.sg43030`, `OAI.UniversalTensorSquare.sg43033`, `OAI.UniversalTensorSquare.sg43041`, `OAI.UniversalTensorSquare.sg43044`, `OAI.UniversalTensorSquare.sg43048`, `OAI.UniversalTensorSquare.sg43049`, `OAI.UniversalTensorSquare.sg43050`, `OAI.UniversalTensorSquare.sg43053`, `OAI.UniversalTensorSquare.sg43054`, `OAI.UniversalTensorSquare.sg43060`, `OAI.UniversalTensorSquare.sg43061`, `OAI.UniversalTensorSquare.sg43068`, `OAI.UniversalTensorSquare.sg43072`, `OAI.UniversalTensorSquare.sg43073`, `OAI.UniversalTensorSquare.sg43076`, `OAI.UniversalTensorSquare.sg43077`, `OAI.UniversalTensorSquare.sg43080`, `OAI.UniversalTensorSquare.sg43081`, `OAI.UniversalTensorSquare.sg43087`, `OAI.UniversalTensorSquare.sg43093`, `OAI.UniversalTensorSquare.sg43094`, `OAI.UniversalTensorSquare.sg43097`, `OAI.UniversalTensorSquare.sg43100`, `OAI.UniversalTensorSquare.sg43101`, `OAI.UniversalTensorSquare.sg43103`, `OAI.UniversalTensorSquare.sg43108`, `OAI.UniversalTensorSquare.sg43111`, `OAI.UniversalTensorSquare.sg43117`, `OAI.UniversalTensorSquare.sg43121`, `OAI.UniversalTensorSquare.sg43123`, `OAI.UniversalTensorSquare.sg43127`, `OAI.UniversalTensorSquare.sg43130`, `OAI.UniversalTensorSquare.sg43132`, `OAI.UniversalTensorSquare.sg43137`, `OAI.UniversalTensorSquare.sg43143`, `OAI.UniversalTensorSquare.sg43149`, `OAI.UniversalTensorSquare.sg43157`, `OAI.UniversalTensorSquare.sg43159`, `OAI.UniversalTensorSquare.sg43164`, `OAI.UniversalTensorSquare.sg43170`, `OAI.UniversalTensorSquare.sg43174`, `OAI.UniversalTensorSquare.sg43177`, `OAI.UniversalTensorSquare.sg43181`, `OAI.UniversalTensorSquare.sg43185`, `OAI.UniversalTensorSquare.sg43193`, `OAI.UniversalTensorSquare.sg43196`, `OAI.UniversalTensorSquare.sg43208`, `OAI.UniversalTensorSquare.sg43211`, `OAI.UniversalTensorSquare.sg43213`, `OAI.UniversalTensorSquare.sg43231`, `OAI.UniversalTensorSquare.sg43235`, `OAI.UniversalTensorSquare.sg43246`, `OAI.UniversalTensorSquare.sg503`, `OAI.UniversalTensorSquare.sg52`, `OAI.UniversalTensorSquare.sg5629`, `OAI.UniversalTensorSquare.sg5630`, `OAI.UniversalTensorSquare.sg5631`, `OAI.UniversalTensorSquare.sg5632`, `OAI.UniversalTensorSquare.sg5633`, `OAI.UniversalTensorSquare.sg5715`, `OAI.UniversalTensorSquare.sg5718`, `OAI.UniversalTensorSquare.sg6405`, `OAI.UniversalTensorSquare.sg6522`, `OAI.UniversalTensorSquare.sg6640`, `OAI.UniversalTensorSquare.sg6641`, `OAI.UniversalTensorSquare.sg6642`, `OAI.UniversalTensorSquare.sg6670`, `OAI.UniversalTensorSquare.sg6676`, `OAI.UniversalTensorSquare.sg6677`, `OAI.UniversalTensorSquare.sg6681`, `OAI.UniversalTensorSquare.sg6682`, `OAI.UniversalTensorSquare.sg6683`, `OAI.UniversalTensorSquare.sg6684`, `OAI.UniversalTensorSquare.sg6688`, `OAI.UniversalTensorSquare.sg6689`, `OAI.UniversalTensorSquare.sg6771`, `OAI.UniversalTensorSquare.sg6773`, `OAI.UniversalTensorSquare.sg6775`, `OAI.UniversalTensorSquare.sg6777`, `OAI.UniversalTensorSquare.sg6779`, `OAI.UniversalTensorSquare.sg6787`, `OAI.UniversalTensorSquare.sg6788`, `OAI.UniversalTensorSquare.sg6821`, `OAI.UniversalTensorSquare.sg6824`, `OAI.UniversalTensorSquare.sg6868`, `OAI.UniversalTensorSquare.sg6872`, `OAI.UniversalTensorSquare.sg6874`, `OAI.UniversalTensorSquare.sg6915`, `OAI.UniversalTensorSquare.sg6918`, `OAI.UniversalTensorSquare.sg6947`, `OAI.UniversalTensorSquare.sg703`, `OAI.UniversalTensorSquare.sg7085`, `OAI.UniversalTensorSquare.sg7089`, `OAI.UniversalTensorSquare.sg7096`, `OAI.UniversalTensorSquare.sg7099`, `OAI.UniversalTensorSquare.sg7156`, `OAI.UniversalTensorSquare.sg7213`, `OAI.UniversalTensorSquare.sg7218`, `OAI.UniversalTensorSquare.sg7247`, `OAI.UniversalTensorSquare.sg7250`, `OAI.UniversalTensorSquare.sg7252`, `OAI.UniversalTensorSquare.sg7307`, `OAI.UniversalTensorSquare.sg7315`, `OAI.UniversalTensorSquare.sg7341`, `OAI.UniversalTensorSquare.sg7347`, `OAI.UniversalTensorSquare.sg7349`, `OAI.UniversalTensorSquare.sg7350`, `OAI.UniversalTensorSquare.sg7356`, `OAI.UniversalTensorSquare.sg7357`, `OAI.UniversalTensorSquare.sg7358`, `OAI.UniversalTensorSquare.sg7359`, `OAI.UniversalTensorSquare.sg7365`, `OAI.UniversalTensorSquare.sg7528`, `OAI.UniversalTensorSquare.sg7563`, `OAI.UniversalTensorSquare.sg7575`, `OAI.UniversalTensorSquare.sg7578`, `OAI.UniversalTensorSquare.sg7579`, `OAI.UniversalTensorSquare.sg7580`, `OAI.UniversalTensorSquare.sg7582`, `OAI.UniversalTensorSquare.sg7583`, `OAI.UniversalTensorSquare.sg7585`, `OAI.UniversalTensorSquare.sg7587`, `OAI.UniversalTensorSquare.sg7588`, `OAI.UniversalTensorSquare.sg7589`, `OAI.UniversalTensorSquare.sg7590`, `OAI.UniversalTensorSquare.sg7591`, `OAI.UniversalTensorSquare.sg7646`, `OAI.UniversalTensorSquare.sg7648`, `OAI.UniversalTensorSquare.sg7649`, `OAI.UniversalTensorSquare.sg7650`, `OAI.UniversalTensorSquare.sg7651`, `OAI.UniversalTensorSquare.sg7652`, `OAI.UniversalTensorSquare.sg7653`, `OAI.UniversalTensorSquare.sg7654`, `OAI.UniversalTensorSquare.sg7655`, `OAI.UniversalTensorSquare.sg7656`, `OAI.UniversalTensorSquare.sg7657`, `OAI.UniversalTensorSquare.sg7658`, `OAI.UniversalTensorSquare.sg7711`, `OAI.UniversalTensorSquare.sg7712`, `OAI.UniversalTensorSquare.sg7713`, `OAI.UniversalTensorSquare.sg7714`, `OAI.UniversalTensorSquare.sg7715`, `OAI.UniversalTensorSquare.sg7716`, `OAI.UniversalTensorSquare.sg7717`, `OAI.UniversalTensorSquare.sg7718`, `OAI.UniversalTensorSquare.sg7719`, `OAI.UniversalTensorSquare.sg7899`, `OAI.UniversalTensorSquare.sg7901`, `OAI.UniversalTensorSquare.sg7907`, `OAI.UniversalTensorSquare.sg7909`, `OAI.UniversalTensorSquare.sg7913`, `OAI.UniversalTensorSquare.sg7917`, `OAI.UniversalTensorSquare.sg7926`, `OAI.UniversalTensorSquare.sg7929`, `OAI.UniversalTensorSquare.sg7930`, `OAI.UniversalTensorSquare.sg7931`, `OAI.UniversalTensorSquare.sg7963`, `OAI.UniversalTensorSquare.sg7967`, `OAI.UniversalTensorSquare.sg7968`, `OAI.UniversalTensorSquare.sg7978`, `OAI.UniversalTensorSquare.sg8011`, `OAI.UniversalTensorSquare.sg8012`, `OAI.UniversalTensorSquare.sg8013`, `OAI.UniversalTensorSquare.sg8018`, `OAI.UniversalTensorSquare.sg8430`, `OAI.UniversalTensorSquare.sg8465`, `OAI.UniversalTensorSquare.sg8467`, `OAI.UniversalTensorSquare.sg8559`, `OAI.UniversalTensorSquare.sg8626`, `OAI.UniversalTensorSquare.sg8665`, `OAI.UniversalTensorSquare.sg9093`, `OAI.UniversalTensorSquare.sg9095`, `OAI.UniversalTensorSquare.sg9108`, `OAI.UniversalTensorSquare.sg9240`, `OAI.UniversalTensorSquare.sg9245`, `OAI.UniversalTensorSquare.sg9247`, `OAI.UniversalTensorSquare.sg9259`, `OAI.UniversalTensorSquare.sg9349`, `OAI.UniversalTensorSquare.sg9350`, `OAI.UniversalTensorSquare.sg9358`, `OAI.UniversalTensorSquare.sg9359`, `OAI.UniversalTensorSquare.sg9461`, `OAI.UniversalTensorSquare.sg9493`, `OAI.UniversalTensorSquare.sg9510`, `OAI.UniversalTensorSquare.sg9520`, `OAI.UniversalTensorSquare.sg9528`, `OAI.UniversalTensorSquare.sg9529`, `OAI.UniversalTensorSquare.sg9530`, `OAI.UniversalTensorSquare.sg9554`, `OAI.UniversalTensorSquare.sg9590`, `OAI.UniversalTensorSquare.sg9618`, `OAI.UniversalTensorSquare.sg9619`, `OAI.UniversalTensorSquare.sg9727`, `OAI.UniversalTensorSquare.sg9734`, `OAI.UniversalTensorSquare.sg9742`, `OAI.UniversalTensorSquare.sg9745`, `OAI.UniversalTensorSquare.sg9746`, `OAI.UniversalTensorSquare.sg9748`, `OAI.UniversalTensorSquare.sg9753`, `OAI.UniversalTensorSquare.sg9755`, `OAI.UniversalTensorSquare.sg9756`, `OAI.UniversalTensorSquare.sg9759`, `OAI.UniversalTensorSquare.sg9761`, `OAI.UniversalTensorSquare.sg9818`, `OAI.UniversalTensorSquare.sg9833`, `OAI.UniversalTensorSquare.sg9835`, `OAI.UniversalTensorSquare.sg9857`, `OAI.UniversalTensorSquare.smallCert13_24`, `OAI.UniversalTensorSquare.smallCert13_30`, `OAI.UniversalTensorSquare.smallCert13_4`, `OAI.UniversalTensorSquare.smallCert13_5`, `OAI.UniversalTensorSquare.smallCert13_6`, `OAI.UniversalTensorSquare.smallCert13_7`, `OAI.UniversalTensorSquare.smallSupport11_0`, `OAI.UniversalTensorSquare.smallSupport11_12`, `OAI.UniversalTensorSquare.smallSupport11_13`, `OAI.UniversalTensorSquare.smallSupport11_14`, `OAI.UniversalTensorSquare.smallSupport11_15`, `OAI.UniversalTensorSquare.smallSupport11_17`, `OAI.UniversalTensorSquare.smallSupport11_18`, `OAI.UniversalTensorSquare.smallSupport11_23`, `OAI.UniversalTensorSquare.smallSupport11_25`, `OAI.UniversalTensorSquare.smallSupport11_27`, `OAI.UniversalTensorSquare.smallSupport11_4`, `OAI.UniversalTensorSquare.smallSupport11_5`, `OAI.UniversalTensorSquare.smallSupport11_6`, `OAI.UniversalTensorSquare.smallSupport11_7`, `OAI.UniversalTensorSquare.smallSupport11_9`, `OAI.UniversalTensorSquare.smallSupport13_0`, `OAI.UniversalTensorSquare.smallSupport13_1`, `OAI.UniversalTensorSquare.smallSupport13_10`, `OAI.UniversalTensorSquare.smallSupport13_11`, `OAI.UniversalTensorSquare.smallSupport13_12`, `OAI.UniversalTensorSquare.smallSupport13_13`, `OAI.UniversalTensorSquare.smallSupport13_14`, `OAI.UniversalTensorSquare.smallSupport13_15`, `OAI.UniversalTensorSquare.smallSupport13_16`, `OAI.UniversalTensorSquare.smallSupport13_17`, `OAI.UniversalTensorSquare.smallSupport13_18`, `OAI.UniversalTensorSquare.smallSupport13_19`, `OAI.UniversalTensorSquare.smallSupport13_2`, `OAI.UniversalTensorSquare.smallSupport13_20`, `OAI.UniversalTensorSquare.smallSupport13_21`, `OAI.UniversalTensorSquare.smallSupport13_22`, `OAI.UniversalTensorSquare.smallSupport13_23`, `OAI.UniversalTensorSquare.smallSupport13_24`, `OAI.UniversalTensorSquare.smallSupport13_26`, `OAI.UniversalTensorSquare.smallSupport13_27`, `OAI.UniversalTensorSquare.smallSupport13_28`, `OAI.UniversalTensorSquare.smallSupport13_29`, `OAI.UniversalTensorSquare.smallSupport13_3`, `OAI.UniversalTensorSquare.smallSupport13_30`, `OAI.UniversalTensorSquare.smallSupport13_32`, `OAI.UniversalTensorSquare.smallSupport13_33`, `OAI.UniversalTensorSquare.smallSupport13_34`, `OAI.UniversalTensorSquare.smallSupport13_35`, `OAI.UniversalTensorSquare.smallSupport13_36`, `OAI.UniversalTensorSquare.smallSupport13_37`, `OAI.UniversalTensorSquare.smallSupport13_38`, `OAI.UniversalTensorSquare.smallSupport13_39`, `OAI.UniversalTensorSquare.smallSupport13_4`, `OAI.UniversalTensorSquare.smallSupport13_40`, `OAI.UniversalTensorSquare.smallSupport13_43`, `OAI.UniversalTensorSquare.smallSupport13_44`, `OAI.UniversalTensorSquare.smallSupport13_45`, `OAI.UniversalTensorSquare.smallSupport13_47`, `OAI.UniversalTensorSquare.smallSupport13_48`, `OAI.UniversalTensorSquare.smallSupport13_49`, `OAI.UniversalTensorSquare.smallSupport13_5`, `OAI.UniversalTensorSquare.smallSupport13_50`, `OAI.UniversalTensorSquare.smallSupport13_6`, `OAI.UniversalTensorSquare.smallSupport13_7`, `OAI.UniversalTensorSquare.smallSupport13_9`, `OAI.UniversalTensorSquare.smallSupports11` and `OAI.UniversalTensorSquare.smallSupports13`.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/RepresentationTheory at commit 7ef5c0c

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US000
import Definitions.Def_OAIQ259US001

section
-- module Solutions.OAIQ259_US.Saxl_Model
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uG uV

namespace Saxl

/- Coefficients of position tensors on an alphabet of size `d`. -/


def SaxlConjecture : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ (μ : YoungDiagram) (hμ : μ.card = (staircase m).card),
    0 < kronecker (canonicalTableau (staircase m) rfl)
      (canonicalTableau (staircase m) rfl) (canonicalTableau μ hμ)

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_Polytabloid
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.Columns.columnTableau_val _root_.OAI.Saxl.coordinateProjection_apply _root_.OAI.Saxl.positionTensor_tmul _root_.OAI.Saxl.relabelWord_apply _root_.OAI.Saxl.tableauInclusion_cell _root_.OAI.Saxl.tableauMove_apply _root_.OAI.Saxl.tableauMove_inv_apply _root_.OAI.Saxl.wordMap_single _root_.OAI.Saxl.wordRep_star _root_.OAI.Saxl.wordTensor_tmul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uX

namespace Saxl

/- A finite set is the unique maximizer of its strictly signed separator.
Used below for the Ferrers equality case in the Specht submodule theorem. -/
def columnAlt {n d : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    Module.End ℂ (WordSpace n d) := by
  classical
  letI := Fintype.ofFinite (columnGroup t)
  exact ∑ g : columnGroup t,
    signC (g : Equiv.Perm (Fin n)) • wordRep n d (g : Equiv.Perm (Fin n))

lemma columnAlt_mul {n d : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (h : columnGroup t) :
    columnAlt (d := d) t * wordRep n d (h : Equiv.Perm (Fin n)) =
      signC (h : Equiv.Perm (Fin n)) • columnAlt t := by
  classical
  let := Fintype.ofFinite (columnGroup t)
  unfold columnAlt
  simp only [Finset.sum_mul, smul_mul_assoc, Finset.smul_sum]
  symm
  apply (Equiv.sum_comp (Equiv.mulRight h) _).symm.trans
  apply Finset.sum_congr rfl
  intro g hg
  change signC (h : Equiv.Perm (Fin n)) •
    signC ((g * h : columnGroup t) : Equiv.Perm (Fin n)) •
      wordRep n d ((g * h : columnGroup t) : Equiv.Perm (Fin n)) = _
  simp only [Subgroup.coe_mul, map_mul, smul_smul]
  congr 1
  calc signC (h : Equiv.Perm (Fin n)) *
      (signC (g : Equiv.Perm (Fin n)) * signC (h : Equiv.Perm (Fin n))) =
      signC (g : Equiv.Perm (Fin n)) *
        (signC (h : Equiv.Perm (Fin n)) * signC (h : Equiv.Perm (Fin n))) := by ring
    _ = signC (g : Equiv.Perm (Fin n)) := by rw [signC_mul_self, mul_one]

lemma columnAlt_row {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    columnAlt t (Pi.single (rowWord t) 1) = polytabloid t := by
  simp [columnAlt, polytabloid, LinearMap.sum_apply]

/- Construction of the witnessing column rearrangement. -/
lemma column_rearrangement {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (g : Equiv.Perm (Fin n))
    (hinj : Function.Injective (fun i => ((t (g i)).val.1, (t i).val.2))) :
    ∃ h : columnGroup t, rowWord t ∘ g = rowWord t ∘ (h : Equiv.Perm (Fin n)) := by
  classical
  let f : Fin n → Fin n := fun i =>
    t.symm ⟨((t (g i)).val.1, (t i).val.2), ferrers_rearrangement t g hinj i⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply hinj
    have hh := congrArg (fun k => (t k).val) hij
    simpa [f] using hh
  let h : Equiv.Perm (Fin n) := Equiv.ofBijective f ⟨hf, Finite.surjective_of_injective hf⟩
  have hcol : h ∈ columnGroup t := by
    intro i
    change (t (f i)).val.2 = _
    simp [f]
  refine ⟨⟨h, hcol⟩, ?_⟩
  funext i
  apply Fin.ext
  change (t (g i)).val.1 = (t (f i)).val.1
  simp [f]

lemma columnAlt_collision {n d : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (a : Fin n → Fin d) (i j : Fin n) (hij : i ≠ j)
    (hc : (t i).val.2 = (t j).val.2) (ha : a i = a j) :
    columnAlt t (Pi.single a (1 : ℂ)) = 0 := by
  classical
  let h : columnGroup t := ⟨Equiv.swap i j, fun k => Equiv.apply_swap_eq_self (v := fun l => (t l).val.2) hc k⟩
  have hs : signC (h : Equiv.Perm (Fin n)) = -1 := by
    simp [h, signC_def, Equiv.Perm.sign_swap hij]
  have hf : wordRep n d (h : Equiv.Perm (Fin n)) (Pi.single a 1) = Pi.single a 1 := by
    rw [wordRep_single]
    congr 1
    funext k
    exact Equiv.apply_swap_eq_self ha k
  have hh := congrArg (fun f : Module.End ℂ (WordSpace n d) => f (Pi.single a 1))
    (columnAlt_mul (d := d) t h)
  simp only [Module.End.mul_apply, hf, LinearMap.smul_apply, hs, neg_one_smul] at hh
  ext b
  exact CharZero.eq_neg_self_iff.mp (congrFun hh b)

lemma columnAlt_column {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (h : columnGroup t) :
    columnAlt t (Pi.single (rowWord t ∘ (h : Equiv.Perm (Fin n))) 1) =
      signC (h : Equiv.Perm (Fin n)) • polytabloid t := by
  classical
  have he : wordRep n (μ.colLen 0) ((h⁻¹ : columnGroup t) : Equiv.Perm (Fin n))
      (Pi.single (rowWord t) 1) =
      Pi.single (rowWord t ∘ (h : Equiv.Perm (Fin n))) 1 := by
    rw [wordRep_single]
    simp only [Subgroup.coe_inv, inv_inv]
  rw [← he, ← Module.End.mul_apply, columnAlt_mul, LinearMap.smul_apply,
    columnAlt_row, Subgroup.coe_inv, signC_inv]

lemma columnAlt_single {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (g : Equiv.Perm (Fin n)) :
    columnAlt t (Pi.single (rowWord t ∘ g) 1) ∈
      Submodule.span ℂ {polytabloid t} := by
  classical
  by_cases hi : Function.Injective (fun i : Fin n => ((t (g i)).val.1, (t i).val.2))
  · obtain ⟨h, hh⟩ := column_rearrangement t g hi
    rw [hh, columnAlt_column]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  · simp only [Function.Injective] at hi
    push Not at hi
    obtain ⟨i, j, hc, hij⟩ := hi
    have ha : (rowWord t ∘ g) i = (rowWord t ∘ g) j := by
      apply Fin.ext
      have hh := congrArg Prod.fst hc
      exact hh
    have hcol := congrArg Prod.snd hc
    rw [columnAlt_collision t _ i j hij hcol ha]
    exact Submodule.zero_mem _

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_SpechtSubmodule
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.Columns.columnTableau_val _root_.OAI.Saxl.coordinateProjection_apply _root_.OAI.Saxl.positionTensor_tmul _root_.OAI.Saxl.relabelWord_apply _root_.OAI.Saxl.tableauInclusion_cell _root_.OAI.Saxl.tableauMove_apply _root_.OAI.Saxl.tableauMove_inv_apply _root_.OAI.Saxl.wordMap_single _root_.OAI.Saxl.wordTensor_tmul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uG uV

namespace Saxl

lemma columnAlt_mem {n d : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (P : Subrepresentation (wordRep n d)) {x : WordSpace n d} (hx : x ∈ P) :
    columnAlt t x ∈ P := by
  classical
  unfold columnAlt
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  exact Submodule.sum_mem _ (fun g _ =>
    Submodule.smul_mem _ _ (P.apply_mem_toSubmodule (g : Equiv.Perm (Fin n)) hx))

lemma spechtSub_le_tabloidSub {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    spechtSub t ≤ tabloidSub t := by
  apply (cyclic_le _ _ _).mpr
  rw [← columnAlt_row]
  exact columnAlt_mem t (tabloidSub t) (mem_cyclic _ _)

/- The Ferrers shape forces the column antisymmetrizer to have rank one
on the row-tabloid module. -/
lemma columnAlt_tabloid {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    {x : WordSpace n (μ.colLen 0)} (hx : x ∈ tabloidSub t) :
    columnAlt t x ∈ Submodule.span ℂ {polytabloid t} := by
  classical
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    dsimp only
    rw [wordRep_single]
    exact columnAlt_single t g⁻¹
  | zero => simpa only [map_zero] using (Submodule.zero_mem (Submodule.span ℂ {polytabloid t}))
  | add x y hx hy ihx ihy =>
    simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul c x hx ih =>
    simpa only [map_smul] using Submodule.smul_mem _ c ih

lemma polytabloid_real {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    star (polytabloid t) = polytabloid t := by
  classical
  unfold polytabloid
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro g hg
  rw [star_smul, wordRep_star]
  simp only [star_intCast]
  congr 2
  ext a
  simp [Pi.single_apply]

lemma cyclic_star {n d : ℕ} (v : WordSpace n d) (hv : star v = v)
    {x : WordSpace n d} (hx : x ∈ cyclic (wordRep n d) v) :
    star x ∈ cyclic (wordRep n d) v := by
  change star x ∈ (cyclic (wordRep n d) v).toSubmodule
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    dsimp only
    rw [wordRep_star, hv]
    exact (cyclic (wordRep n d) v).apply_mem_toSubmodule g (mem_cyclic _ _)
  | zero => simpa only [star_zero] using (Submodule.zero_mem (cyclic (wordRep n d) v).toSubmodule)
  | add x y hx hy ihx ihy =>
    simpa only [star_add] using Submodule.add_mem _ ihx ihy
  | smul c x hx ih =>
    simpa only [star_smul] using Submodule.smul_mem _ (star c) ih

/- On words, precomposition by a position permutation is a bijection. -/

lemma wordPair_move {n d : ℕ} (g : Equiv.Perm (Fin n)) (x y : WordSpace n d) :
    dotProduct (wordRep n d g x) y = dotProduct x (wordRep n d g⁻¹ y) := by
  have hh := Equiv.sum_comp (wordPerm n d g)
    (fun a => x a * y (a ∘ (g⁻¹ : Equiv.Perm (Fin n))))
  simpa [dotProduct, wordPerm, wordRep, Function.comp_assoc] using hh

lemma columnAlt_pair {n d : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (x y : WordSpace n d) :
    dotProduct (columnAlt t x) y = dotProduct x (columnAlt t y) := by
  classical
  let := Fintype.ofFinite (columnGroup t)
  unfold columnAlt
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, sum_dotProduct,
    dotProduct_sum, smul_dotProduct, dotProduct_smul, wordPair_move]
  apply (Equiv.sum_comp (Equiv.inv (columnGroup t)) _).symm.trans
  apply Finset.sum_congr rfl
  intro g hg
  simp only [Equiv.inv_apply, Subgroup.coe_inv, signC_inv, inv_inv]

lemma columnAlt_coefficient {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (x : WordSpace n (μ.colLen 0)) :
    columnAlt t x (rowWord t) = dotProduct x (polytabloid t) := by
  classical
  rw [← dotProduct_single_one (columnAlt t x), columnAlt_pair, columnAlt_row]

lemma polytabloid_ne_zero {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    polytabloid t ≠ 0 := by
  intro h
  have hh := congrFun h (rowWord t)
  rw [polytabloid_rowWord] at hh
  exact one_ne_zero hh

lemma specht_detect {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    {x : WordSpace n (μ.colLen 0)} (hx : x ∈ spechtSub t) (hx0 : x ≠ 0) :
    ∃ g : Equiv.Perm (Fin n), dotProduct (wordRep n (μ.colLen 0) g x) (polytabloid t) ≠ 0 := by
  classical
  by_contra h
  push Not at h
  have hy : ∀ y ∈ (spechtSub t).toSubmodule, dotProduct x y = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨g, rfl⟩ := hy
      have hh := wordPair_move g⁻¹ x (polytabloid t)
      rw [inv_inv] at hh
      exact hh.symm.trans (h g⁻¹)
    | zero => exact dotProduct_zero _
    | add y z hy hz ihy ihz => rw [dotProduct_add, ihy, ihz, add_zero]
    | smul c y hy ih => rw [dotProduct_smul, ih, smul_zero]
  have hs : star x ∈ (spechtSub t).toSubmodule :=
    cyclic_star (polytabloid t) (polytabloid_real t) hx
  let : PartialOrder ℂ := RCLike.toPartialOrder
  let : StarOrderedRing ℂ := RCLike.toStarOrderedRing
  exact hx0 (dotProduct_self_star_eq_zero.mp (hy (star x) hs))

/- Every nonzero vector in the genuine complex Specht cyclic subspace
again generates that whole subspace. -/
theorem specht_cyclic_of_ne_zero {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    {x : WordSpace n (μ.colLen 0)} (hx : x ∈ spechtSub t) (hx0 : x ≠ 0) :
    cyclic (wordRep n (μ.colLen 0)) x = spechtSub t := by
  classical
  apply le_antisymm ((cyclic_le _ _ _).mpr hx)
  apply (cyclic_le _ _ _).mpr
  obtain ⟨g, hg⟩ := specht_detect t hx hx0
  have he : wordRep n (μ.colLen 0) g x ∈ spechtSub t :=
    (spechtSub t).apply_mem_toSubmodule g hx
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
    (columnAlt_tabloid t (spechtSub_le_tabloidSub t he))
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hc
    apply hg
    rw [← columnAlt_coefficient, ← hc]
    rfl
  have hh := columnAlt_mem t (cyclic (wordRep n (μ.colLen 0)) x)
    ((cyclic (wordRep n (μ.colLen 0)) x).apply_mem_toSubmodule g (mem_cyclic _ _))
  rw [← hc] at hh
  exact (Submodule.smul_mem_iff _ hc0).mp hh

/- Inclusion of a subrepresentation of a subrepresentation into the ambient space. -/
theorem specht_irreducible {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    Representation.IsIrreducible (spechtRep t) := by
  classical
  have hb : (⊥ : Subrepresentation (spechtRep t)) ≠ ⊤ := by
    intro h
    have hp : (⟨polytabloid t, mem_cyclic _ _⟩ : Specht t) ∈
        (⊥ : Subrepresentation (spechtRep t)).toSubmodule := by
      rw [h]
      trivial
    have he : (⟨polytabloid t, mem_cyclic _ _⟩ : Specht t) = 0 :=
      (Submodule.mem_bot ℂ).mp hp
    exact polytabloid_ne_zero t (congrArg Subtype.val he)
  let : Nontrivial (Subrepresentation (spechtRep t)) := ⟨⟨⊥, ⊤, hb⟩⟩
  apply IsSimpleOrder.of_forall_eq_top
  intro S hS
  have hn : S.toSubmodule ≠ ⊥ := by
    intro h
    exact hS (Subrepresentation.toSubmodule_injective h)
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff S.toSubmodule).mp hn
  have hv : (x : WordSpace n (μ.colLen 0)) ≠ 0 := by
    intro h
    exact hx0 (Subtype.ext h)
  have hl : cyclic (wordRep n (μ.colLen 0)) x.val ≤ subrepAmbient (spechtSub t) S :=
    (cyclic_le _ _ _).mpr ⟨x, hx, rfl⟩
  rw [specht_cyclic_of_ne_zero t x.property hv] at hl
  apply le_antisymm le_top
  intro y hy
  have hm := hl y.property
  obtain ⟨z, hz, he⟩ := hm
  have he' : z = y := Subtype.ext he
  exact he' ▸ hz

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_SpechtDuality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

/- The ordinary bilinear coordinate pairing restricted to any invariant word subspace. -/
def subrepPairMap {n d : ℕ} (S : Subrepresentation (wordRep n d)) :
    Representation.IntertwiningMap S.toRepresentation S.toRepresentation.dual where
  toLinearMap :=
    { toFun := fun x =>
        { toFun := fun y => dotProduct x.val y.val
          map_add' := by intro y z; exact dotProduct_add _ _ _
          map_smul' := by intro a y; exact dotProduct_smul a _ _ }
      map_add' := by intro x y; ext z; exact add_dotProduct _ _ _
      map_smul' := by intro a x; ext z; exact smul_dotProduct a _ _ }
  isIntertwining' g := by
    ext x y
    exact wordPair_move g x.val y.val

lemma subrepPairMap_injective {n d : ℕ} (S : Subrepresentation (wordRep n d))
    (hS : ∀ x ∈ S.toSubmodule, star x ∈ S.toSubmodule) :
    Function.Injective (subrepPairMap S) := by
  classical
  apply (subrepPairMap S).toLinearMap.ker_eq_bot.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  have hh : subrepPairMap S x = 0 := hx
  have hz : dotProduct x.val (star x.val) = 0 :=
    congrArg (fun f : Module.Dual ℂ S.toSubmodule => f ⟨star x.val, hS x.val x.property⟩) hh
  let : PartialOrder ℂ := RCLike.toPartialOrder
  let : StarOrderedRing ℂ := RCLike.toStarOrderedRing
  exact Subtype.ext (dotProduct_self_star_eq_zero.mp hz)

/- Complex conjugation-stable invariant word subspaces are canonically self-dual
via bilinear evaluation, yielding equivariant projections. -/
def subrepSelfDual {n d : ℕ} (S : Subrepresentation (wordRep n d))
    (hS : ∀ x ∈ S.toSubmodule, star x ∈ S.toSubmodule) :
    Representation.Equiv S.toRepresentation S.toRepresentation.dual :=
  (subrepPairMap S).ofBijective
    ⟨subrepPairMap_injective S hS,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (Subspace.dual_finrank_eq (K := ℂ) (V := S.toSubmodule)).symm).mp (subrepPairMap_injective S hS)⟩

/- Actual self-duality of every complex Specht representation. -/
def spechtSelfDual {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    Representation.Equiv (spechtRep t) (spechtRep t).dual :=
  subrepSelfDual (spechtSub t) (fun _ hx => cyclic_star _ (polytabloid_real t) hx)

/- Restriction of the ambient bilinear coordinate pairing to an invariant subspace. -/
def subrepPairFromAmbient {n d : ℕ} (S : Subrepresentation (wordRep n d)) :
    Representation.IntertwiningMap (wordRep n d) S.toRepresentation.dual where
  toLinearMap :=
    { toFun := fun x =>
        { toFun := fun y => dotProduct x y.val
          map_add' := by intro y z; exact dotProduct_add _ _ _
          map_smul' := by intro a y; exact dotProduct_smul a _ _ }
      map_add' := by intro x y; ext z; exact add_dotProduct _ _ _
      map_smul' := by intro a x; ext z; exact smul_dotProduct a _ _ }
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    exact wordPair_move g x y.val

/- The genuine equivariant orthogonal-coordinate projection. -/
def subrepProject {n d : ℕ} (S : Subrepresentation (wordRep n d))
    (hS : ∀ x ∈ S.toSubmodule, star x ∈ S.toSubmodule) :
    Representation.IntertwiningMap (wordRep n d) S.toRepresentation :=
  (subrepSelfDual S hS).symm.toIntertwiningMap.comp (subrepPairFromAmbient S)

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_HighProjection
attribute [-simp] _root_.OAI.Saxl.staircase_colLen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl
/- Translate the high part of each row to the smaller staircase. -/
def rotateRowCell (h s : ℕ) (x : (staircase (h+s)).cells) : (staircase (h+s)).cells :=
  ⟨(x.val.1, if x.val.2 < h - x.val.1 then x.val.2+s else x.val.2-(h-x.val.1)), by
    have hx : x.val.1 + x.val.2 < h+s := mem_staircase.mp x.property
    apply mem_staircase.mpr
    split_ifs <;> omega⟩

lemma rotateRowCell_injective (h s : ℕ) : Function.Injective (rotateRowCell h s) := by
  intro x y he
  have hi0 := congrArg (fun z : (staircase (h+s)).cells => z.val.1) he
  have hi : x.val.1 = y.val.1 := hi0
  have hj := congrArg (fun z : (staircase (h+s)).cells => z.val.2) he
  have hx : x.val.1 + x.val.2 < h+s := mem_staircase.mp x.property
  have hy : y.val.1 + y.val.2 < h+s := mem_staircase.mp y.property
  dsimp [rotateRowCell] at hj
  apply Subtype.ext
  apply Prod.ext hi
  split_ifs at hj <;> omega

def rotateRow (h s : ℕ) : Equiv.Perm (staircase (h+s)).cells :=
  Equiv.ofBijective (rotateRowCell h s) (⟨rotateRowCell_injective h s, Finite.surjective_of_injective (rotateRowCell_injective h s)⟩)

def rotateColumn (h s : ℕ) : Equiv.Perm (staircase (h+s)).cells :=
  ((staircaseSwap (h+s)).trans (rotateRow h s)).trans (staircaseSwap (h+s))

def rotateRowPositions (h s : ℕ) : columnGroup (stairRowTableau (h+s)) :=
  ⟨((stairTableau (h+s)).trans (rotateRow h s)).trans (stairTableau (h+s)).symm, by
    intro i
    change (stairTableau (h+s) ((stairTableau (h+s)).symm (rotateRow h s (stairTableau (h+s) i)))).val.1 = _
    simp only [Equiv.apply_symm_apply]
    rfl⟩

def rotateColumnPositions (h s : ℕ) : columnGroup (stairTableau (h+s)) :=
  ⟨((stairTableau (h+s)).trans (rotateColumn h s)).trans (stairTableau (h+s)).symm, by
    intro i
    change (stairTableau (h+s) ((stairTableau (h+s)).symm (rotateColumn h s (stairTableau (h+s) i)))).val.2 = _
    simp only [Equiv.apply_symm_apply]
    rfl⟩

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_CoordinateSector
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.positionTensor_tmul _root_.OAI.Saxl.relabelWord_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl
/- Coordinate projection; equivariance is asserted only for preserved predicates. -/

lemma coordinateProjection_single {n d : ℕ} (P : (Fin n → Fin d) → Prop)
    (a : Fin n → Fin d) [Decidable (P a)] :
    coordinateProjection P (Pi.single a 1) = if P a then Pi.single a 1 else 0 := by
  classical
  ext b
  by_cases he : b = a
  · subst b; by_cases h : P a <;> simp [h]
  · by_cases h : P a <;> simp [he, h]

/- Permutations preserving a position sector. -/
def altWord {n d : ℕ} (G : Subgroup (Equiv.Perm (Fin n))) (a : Fin n → Fin d) :
    WordSpace n d := by
  classical
  letI := Fintype.ofFinite G
  exact ∑ g : G, signC (g : Equiv.Perm (Fin n)) •
    wordRep n d (g : Equiv.Perm (Fin n)) (Pi.single a 1)

end Saxl

namespace Saxl
/- The prescribed high sector in the actual staircase enumeration. -/
def stairHigh (h s : ℕ) (i : Fin (staircase (h+s)).card) : Prop :=
  (stairTableau (h+s) i).val.1 + (stairTableau (h+s) i).val.2 < h

lemma polytabloid_eq_altWord {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    polytabloid t = altWord (columnGroup t) (rowWord t) := rfl

/- The cut's two layers, with their exact retained row and column permutations. -/
def cutRowWord (h s : ℕ) :=
  altWord (columnGroup (stairRowTableau (h+s)) ⊓ sectorGroup (stairHigh h s))
    (rowWord (stairRowTableau (h+s)) ∘ (rotateRowPositions h s : Equiv.Perm _))

def cutColumnWord (h s : ℕ) :=
  altWord (columnGroup (stairTableau (h+s)) ⊓ sectorGroup (stairHigh h s))
    (rowWord (stairTableau (h+s)) ∘ (rotateColumnPositions h s : Equiv.Perm _))

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_PositionSplit
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.joinPositions_parts _root_.OAI.Saxl.leftWord_join _root_.OAI.Saxl.pairWordsEquiv_apply _root_.OAI.Saxl.positionTensor_tmul _root_.OAI.Saxl.relabelWord_apply _root_.OAI.Saxl.rightWord_join _root_.OAI.Saxl.sumPerm_mul _root_.OAI.Saxl.sumPerm_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uAlpha

namespace Saxl
/- The genuine product position permutation under a disjoint-set enumeration. -/

lemma word_eq_iff_parts {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (w v : Fin n → Fin d) : w = v ↔ leftWord e w = leftWord e v ∧ rightWord e w = rightWord e v := by
  constructor
  · rintro rfl; exact ⟨rfl,rfl⟩
  · rintro ⟨h₁,h₂⟩
    funext i
    obtain ⟨k, rfl⟩ := e.symm.surjective i
    cases k with
    | inl k => exact congrFun h₁ k
    | inr k => exact congrFun h₂ k

lemma single_positionProduct {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (w : Fin n → Fin d) :
    (Pi.single w (1:ℂ) : WordSpace n d) =
      positionProduct e (Pi.single (leftWord e w) 1) (Pi.single (rightWord e w) 1) := by
  classical
  ext v
  simp only [positionProduct, Pi.single_apply]
  simp only [word_eq_iff_parts e]
  split_ifs <;> simp_all

lemma sumPerm_injective {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b) :
    Function.Injective (fun p : Equiv.Perm (Fin a) × Equiv.Perm (Fin b) => sumPerm e p.1 p.2) := by
  intro p q hpq
  apply Prod.ext
  · apply Equiv.ext
    intro i
    have h := congrArg (fun g : Equiv.Perm (Fin n) => e (g (e.symm (Sum.inl i)))) hpq
    simpa using h
  · apply Equiv.ext
    intro i
    have h := congrArg (fun g : Equiv.Perm (Fin n) => e (g (e.symm (Sum.inr i)))) hpq
    simpa using h

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_BandFactorization
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.Columns.columnTableau_val _root_.OAI.Saxl.positionTensor_tmul _root_.OAI.Saxl.relabelWord_apply _root_.OAI.Saxl.tableauInclusion_cell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

def highPositionsEquiv (h s : ℕ) :
    {i : Fin (staircase (h+s)).card // stairHigh h s i} ≃ Fin (staircase h).card where
  toFun i := (stairTableau h).symm ⟨(stairTableau (h+s) i.val).val, mem_staircase.mpr i.property⟩
  invFun j := ⟨(stairTableau (h+s)).symm ⟨(stairTableau h j).val, by
    apply mem_staircase.mpr
    have := mem_staircase.mp (stairTableau h j).property
    omega⟩, by
      change ((stairTableau (h+s)) ((stairTableau (h+s)).symm _)).val.1 +
        ((stairTableau (h+s)) ((stairTableau (h+s)).symm _)).val.2 < h
      simp only [Equiv.apply_symm_apply]
      exact mem_staircase.mp (stairTableau h j).property⟩
  left_inv i := by apply Subtype.ext; simp
  right_inv i := by simp

abbrev bandSize (h s : ℕ) := Nat.card {i : Fin (staircase (h+s)).card // ¬stairHigh h s i}

def cutPositions (h s : ℕ) :
    Fin (staircase (h+s)).card ≃ Fin (staircase h).card ⊕ Fin (bandSize h s) := by
  classical
  exact (Equiv.sumCompl (stairHigh h s)).symm.trans
    (Equiv.sumCongr (highPositionsEquiv h s) (Fintype.equivFinOfCardEq (show Fintype.card {i : Fin (staircase (h+s)).card // ¬stairHigh h s i} = bandSize h s from Fintype.card_eq_nat_card)))

lemma cutPositions_high (h s : ℕ) (i : Fin (staircase (h+s)).card) :
    (cutPositions h s i).isLeft = true ↔ stairHigh h s i := by
  classical
  by_cases hi : stairHigh h s i <;> simp [cutPositions, Equiv.sumCompl, Equiv.sumCongr, hi]

def bandTableau (h s : ℕ) (j : Fin (bandSize h s)) : (staircase (h+s)).cells :=
  stairTableau (h+s) ((cutPositions h s).symm (Sum.inr j))

def bandRowGroup (h s : ℕ) := fiberGroup (fun j => (bandTableau h s j).val.1)
def bandColumnGroup (h s : ℕ) := fiberGroup (fun j => (bandTableau h s j).val.2)

def highLetter (h s : ℕ) : Fin ((staircase h).colLen 0) → Fin ((staircase (h+s)).colLen 0) :=
  fun a => ⟨a.val+s, by have := a.isLt; simp only [staircase_colLen, Nat.sub_zero] at *; omega⟩

lemma letterLift_single {n d e : ℕ} (f : Fin d → Fin e) (a : Fin n → Fin d) :
    letterLift f (Pi.single a 1) = Pi.single (f ∘ a) (1:ℂ) := by
  classical
  ext b
  rw [letterLift, wordMap_single, Pi.single_apply]
  by_cases he : b = f ∘ a
  · subst b; simp
  · rw [ite_eq_right he]
    have hn : ∃ i, f (a i) ≠ b i := by
      by_contra hh
      push Not at hh
      exact he (funext (fun i => (hh i).symm))
    obtain ⟨i,hi⟩ := hn
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

def bandRowWord (h s : ℕ) : WordSpace (bandSize h s) ((staircase (h+s)).colLen 0) :=
  altWord (bandRowGroup h s) (rightWord (cutPositions h s)
    (rowWord (stairRowTableau (h+s)) ∘ (rotateRowPositions h s : Equiv.Perm _)))

def bandColumnWord (h s : ℕ) : WordSpace (bandSize h s) ((staircase (h+s)).colLen 0) :=
  altWord (bandColumnGroup h s) (rightWord (cutPositions h s)
    (rowWord (stairTableau (h+s)) ∘ (rotateColumnPositions h s : Equiv.Perm _)))



lemma bandTableau_bounds (h s : ℕ) (j : Fin (bandSize h s)) :
    h ≤ (bandTableau h s j).val.1 + (bandTableau h s j).val.2 ∧
      (bandTableau h s j).val.1 + (bandTableau h s j).val.2 < h+s := by
  refine ⟨?_,mem_staircase.mp (bandTableau h s j).property⟩
  have hh := cutPositions_high h s ((cutPositions h s).symm (Sum.inr j))
  simp only [Equiv.apply_symm_apply, Sum.isLeft_inr, Bool.false_eq_true, false_iff] at hh
  change ¬ (bandTableau h s j).val.1 + (bandTableau h s j).val.2 < h at hh
  omega

def bandCellsEquiv (h s : ℕ) : Fin (bandSize h s) ≃
    {c : ℕ × ℕ // h ≤ c.1+c.2 ∧ c.1+c.2 < h+s} :=
  Equiv.ofBijective (fun j => ⟨(bandTableau h s j).val,bandTableau_bounds h s j⟩) (by
    constructor
    · intro i j hij
      have hh : bandTableau h s i = bandTableau h s j := Subtype.ext (congrArg (fun c : {c : ℕ × ℕ // h ≤ c.1+c.2 ∧ c.1+c.2 < h+s} => c.val) hij)
      exact Sum.inr.inj ((cutPositions h s).symm.injective ((stairTableau (h+s)).injective hh))
    · intro c
      let x : (staircase (h+s)).cells := ⟨c.val,mem_staircase.mpr c.property.2⟩
      let i := (stairTableau (h+s)).symm x
      have hi : ¬ stairHigh h s i := by
        change ¬ (stairTableau (h+s) ((stairTableau (h+s)).symm x)).val.1 +
          (stairTableau (h+s) ((stairTableau (h+s)).symm x)).val.2 < h
        simp only [Equiv.apply_symm_apply]
        exact Nat.not_lt.mpr c.property.1
      have he := cutPositions_high h s i
      cases hp : cutPositions h s i with
      | inl j => simp only [hp, Sum.isLeft_inl, true_iff] at he; exact False.elim (hi he)
      | inr j =>
        refine ⟨j, ?_⟩
        apply Subtype.ext
        have hj : (cutPositions h s).symm (Sum.inr j) = i := by rw [← hp,Equiv.symm_apply_apply]
        change (stairTableau (h+s) ((cutPositions h s).symm (Sum.inr j))).val = c.val
        rw [hj]
        exact congrArg Subtype.val ((stairTableau (h+s)).apply_symm_apply x))

def bandPathEquiv (h : ℕ) : Fin (2*(h+1)+1) ≃ Fin (bandSize h 2) :=
  (pathCellsEquiv h).trans (bandCellsEquiv h 2).symm

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_PathAlternation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uAlpha

namespace Saxl.PathLayer

def rowAlt (r : ℕ) : Saxl.WordSpace (2*r+1) 2 :=
  Saxl.altWord (Saxl.fiberGroup (@tag r)) (@base r)

end Saxl.PathLayer

namespace Saxl

def fiberRelabel {n m : ℕ} {α : Type uAlpha} (e : Fin n ≃ Fin m) (c : Fin m → α) :
    fiberGroup (c ∘ e) ≃ fiberGroup c where
  toFun g := ⟨e.permCongr g.val, by
    intro i
    obtain ⟨j,rfl⟩ := e.surjective i
    change c (e (g.val (e.symm (e j)))) = c (e j)
    rw [Equiv.symm_apply_apply]
    exact g.property j⟩
  invFun g := ⟨e.symm.permCongr g.val, by
    intro i
    change c (e (e.symm (g.val (e i)))) = c (e i)
    rw [Equiv.apply_symm_apply]
    exact g.property (e i)⟩
  left_inv g := by apply Subtype.ext; ext i; simp [Equiv.permCongr]
  right_inv g := by apply Subtype.ext; ext i; simp [Equiv.permCongr]



def lowLetter (h : ℕ) : Fin 2 → Fin ((staircase (h+2)).colLen 0) :=
  fun i => ⟨i.val, by rw [staircase_colLen]; have := i.isLt; omega⟩

def bandColumnPathEquiv (h : ℕ) : Fin (2*(h+1)+1) ≃ Fin (bandSize h 2) :=
  Fin.revPerm.trans (bandPathEquiv h)

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_ColumnContraction
attribute [-simp] _root_.OAI.Saxl.tableauInclusion_cell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl.Columns
/- A concrete ordered disjoint union of consecutive columns. -/

instance cellsFintype : (rs : List ℕ) → Fintype (Cells rs)
  | [] => inferInstanceAs (Fintype Empty)
  | r :: rs => @instFintypeSum (Fin r) (Cells rs) inferInstance (cellsFintype rs)

instance cellsDecEq : (rs : List ℕ) → DecidableEq (Cells rs)
  | [] => inferInstanceAs (DecidableEq Empty)
  | r :: rs => @instDecidableEqSum (Fin r) (Cells rs) inferInstance (cellsDecEq rs)

@[reducible] def Perms : List ℕ → Type
  | [] => Unit
  | r :: rs => Equiv.Perm (Fin r) × Perms rs

instance permsFintype : (rs : List ℕ) → Fintype (Perms rs)
  | [] => inferInstanceAs (Fintype Unit)
  | r :: rs => @instFintypeProd (Equiv.Perm (Fin r)) (Perms rs) inferInstance (permsFintype rs)

def perm : {rs : List ℕ} → Perms rs → Equiv.Perm (Cells rs)
  | [], _ => Equiv.refl _
  | _ :: _, (π, σ) => Equiv.sumCongr π (perm σ)

def sg : {rs : List ℕ} → Perms rs → ℂ
  | [], _ => 1
  | _ :: _, (π, σ) => (((Equiv.Perm.sign π : ℤ) : ℂ)) * sg σ

lemma sign_perm {rs : List ℕ} (π : Perms rs) :
    (((Equiv.Perm.sign (perm π) : ℤ) : ℂ)) = sg π := by
  induction rs with
  | nil => simp [perm, sg]
  | cons r rs ih =>
    obtain ⟨π, σ⟩ := π
    have hh := congrArg (fun u : ℤˣ => ((u : ℤ) : ℂ))
      (Equiv.Perm.sign_sumCongr π (perm σ))
    exact hh.trans (by simp only [Units.val_mul, Int.cast_mul, ih]; rfl)

lemma perm_col {rs : List ℕ} (π : Perms rs) (c : Cells rs) : col (perm π c) = col c := by
  induction rs with
  | nil => exact isEmptyElim c
  | cons r rs ih =>
    obtain ⟨π, σ⟩ := π
    cases c with
    | inl i => rfl
    | inr c => exact congrArg (· + 1) (ih σ c)

def chain (rs : List ℕ) (p : ℕ) (N : ℕ → Band.Mat) (π : Perms rs) : Band.Mat :=
  (List.ofFn fun q : Fin rs.sum => Band.D (p + q.val) (N (row (perm π (enumerate rs q))))).prod

lemma perm_injective (rs : List ℕ) : Function.Injective (@perm rs) := by
  induction rs with
  | nil => exact Function.injective_of_subsingleton _
  | cons r rs ih =>
    rintro ⟨π, σ⟩ ⟨π', σ'⟩ h
    apply Prod.ext
    · apply Equiv.ext
      intro i
      exact Sum.inl.inj (Equiv.congr_fun h (Sum.inl i))
    · apply ih
      apply Equiv.ext
      intro c
      exact Sum.inr.inj (Equiv.congr_fun h (Sum.inr c))

lemma perm_surjective (rs : List ℕ) (g : Equiv.Perm (Cells rs))
    (hg : ∀ c, col (g c) = col c) : ∃ π : Perms rs, perm π = g := by
  induction rs with
  | nil => exact ⟨(), Subsingleton.elim _ _⟩
  | cons r rs ih =>
    have hm : Set.MapsTo g (Set.range Sum.inl) (Set.range Sum.inl) := by
      rintro c ⟨i, rfl⟩
      have hh := hg (Sum.inl i)
      cases h : g (Sum.inl i) with
      | inl j => exact ⟨j, rfl⟩
      | inr c => simp [h, col] at hh
    obtain ⟨⟨π, σ⟩, he⟩ := Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl hm
    have hs : ∀ c : Cells rs, col (σ c) = col c := by
      intro c
      have hh := hg (Sum.inr c)
      rw [← he] at hh
      exact Nat.add_right_cancel hh
    obtain ⟨τ, hτ⟩ := ih σ hs
    exact ⟨(π, τ), by simp only [perm, hτ]; exact he⟩

/- The column-recursive coordinates enumerate the actual Ferrers cells. -/

lemma row_lt (μ : YoungDiagram) (c : Cells μ.transpose.rowLens) : row c < μ.colLen 0 :=
  YoungDiagram.mem_iff_lt_colLen.mp
    (μ.up_left_mem le_rfl (Nat.zero_le _) (toYoung μ c).property)


def columnPerm (μ : YoungDiagram) (π : Perms μ.transpose.rowLens) :
    columnGroup (columnTableau μ) :=
  ⟨(enumerate μ.transpose.rowLens).symm.permCongr (perm π), by
    intro i
    simp only [columnTableau_val, Equiv.permCongr_apply, Equiv.symm_symm,
      Equiv.apply_symm_apply]
    exact perm_col π _⟩

lemma columnPerm_bijective (μ : YoungDiagram) : Function.Bijective (columnPerm μ) := by
  constructor
  · intro π σ h
    apply perm_injective μ.transpose.rowLens
    apply (enumerate μ.transpose.rowLens).symm.permCongr.injective
    exact congrArg Subtype.val h
  · intro g
    let e := enumerate μ.transpose.rowLens
    obtain ⟨π, hπ⟩ := perm_surjective μ.transpose.rowLens (e.permCongr g.val) (by
      intro c
      have hh := g.property (e.symm c)
      simpa only [columnTableau_val, Equiv.permCongr_apply, e, Equiv.apply_symm_apply] using hh)
    refine ⟨π, ?_⟩
    apply Subtype.ext
    change e.symm.permCongr (perm π) = g.val
    rw [hπ]
    apply Equiv.ext
    intro i
    simp [Equiv.permCongr_apply]

def columnEquiv (μ : YoungDiagram) : Perms μ.transpose.rowLens ≃ columnGroup (columnTableau μ) :=
  Equiv.ofBijective (columnPerm μ) (columnPerm_bijective μ)

end Saxl.Columns

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_BandPairing
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.positionTensor_tmul _root_.OAI.Saxl.relabelWord_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl.Path

def chainFunctional (n p : ℕ) : WordSpace n 4 →ₗ[ℂ] Mat where
  toFun x := ∑ w : Fin n → Fin 4, x w • chainML n p (fun i => entry (w i))
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp [smul_smul, Finset.smul_sum]

end Saxl.Path

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_CyclicSector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uG uX uY uZ uV

namespace Saxl

def cyclicMap {G : Type uG} {X : Type uX} {Y : Type uY} [Group G] [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] {ρ : Representation ℂ G X} {σ : Representation ℂ G Y}
    (F : Representation.IntertwiningMap ρ σ) (v : X) :
    Representation.IntertwiningMap (cyclic ρ v).toRepresentation (cyclic σ (F v)).toRepresentation where
  toLinearMap := (F.toLinearMap.comp (cyclic ρ v).toSubmodule.subtype).codRestrict _
    (fun x => intertwiner_cyclic_mem F v x.val x.property)
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact LinearMap.congr_fun (F.isIntertwining' g) x.val

lemma cyclicMap_surjective {G : Type uG} {X : Type uX} {Y : Type uY} [Group G] [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] {ρ : Representation ℂ G X} {σ : Representation ℂ G Y}
    (F : Representation.IntertwiningMap ρ σ) (v : X) : Function.Surjective (cyclicMap F v) := by
  intro y
  have hy := y.property
  change y.val ∈ Submodule.span ℂ _ at hy
  suffices ∃ x : (cyclic ρ v).toSubmodule, (cyclicMap F v x).val = y.val by
    obtain ⟨x,hx⟩ := this
    exact ⟨x,Subtype.ext hx⟩
  generalize hz : y.val = z at hy ⊢
  clear y hz
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨g,rfl⟩ := hz
    refine ⟨(cyclic ρ v).toRepresentation g ⟨v,mem_cyclic _ _⟩, ?_⟩
    change F (ρ g v) = σ g (F v)
    exact LinearMap.congr_fun (F.isIntertwining' g) v
  | zero => exact ⟨0,map_zero F⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨u,hu⟩ := ihx
    obtain ⟨w,hw⟩ := ihy
    refine ⟨u+w, ?_⟩
    change F (u.val+w.val) = _
    rw [map_add,show F u.val = x from hu,show F w.val = y from hw]
  | smul c x hx ih =>
    obtain ⟨u,hu⟩ := ih
    refine ⟨c • u, ?_⟩
    change F (c • u.val) = _
    rw [map_smul,show F u.val = x from hu]

/- A genuine equivariant projection of a cyclic generator transfers every
nonzero constituent map back to the original cyclic module by Maschke. -/

def restrictLetters {n d D : ℕ} (φ : Fin d → Fin D) :
    Representation.IntertwiningMap (wordRep n D) (wordRep n d) where
  toLinearMap :=
    { toFun := fun x w => x (φ ∘ w)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  isIntertwining' g := by ext x w; rfl

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_BandSupport
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.positionTensor_tmul _root_.OAI.Saxl.relabelWord_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

/- Coordinate subrepresentation using only letters with property A. -/
def alphabetSub (n d : ℕ) (A : Fin d → Prop) : Subrepresentation (wordRep n d) where
  toSubmodule :=
    { carrier := {x | ∀ w, (∃ i, ¬ A (w i)) → x w = 0}
      zero_mem' := by intro w hw; rfl
      add_mem' := by intro x y hx hy w hw; change x w+y w=0; rw [hx w hw,hy w hw,add_zero]
      smul_mem' := by intro c x hx w hw; change c*x w=0; rw [hx w hw,mul_zero] }
  apply_mem_toSubmodule g := by
    intro x hx w hw
    obtain ⟨i,hi⟩ := hw
    apply hx (w ∘ g)
    exact ⟨g⁻¹ i, by simpa using hi⟩

lemma letterLift_mem_alphabet {n d D : ℕ} (A : Fin D → Prop)
    (φ : Fin d → Fin D) (hφ : ∀ i, A (φ i)) (x : WordSpace n d) :
    letterLift φ x ∈ alphabetSub n D A := by
  classical
  intro w hw
  obtain ⟨i,hi⟩ := hw
  change (∑ a, x a * ∏ j, (if φ (a j) = w j then (1:ℂ) else 0)) = 0
  apply Finset.sum_eq_zero
  intro a ha
  apply mul_eq_zero_of_right
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  exact ite_eq_right (fun hh : φ (a i) = w i => hi (hh ▸ hφ (a i)))

lemma letterLift_eval {n d D : ℕ} (φ : Fin d → Fin D) (hφ : Function.Injective φ)
    (x : WordSpace n d) (w : Fin n → Fin d) : letterLift φ x (φ ∘ w) = x w := by
  classical
  change (∑ a, x a * ∏ i, (if φ (a i) = φ (w i) then (1:ℂ) else 0)) = x w
  rw [Finset.sum_eq_single w]
  · simp
  · intro a ha haw
    apply mul_eq_zero_of_right
    obtain ⟨i,hi⟩ : ∃ i, a i ≠ w i := by by_contra hh; push Not at hh; exact haw (funext hh)
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact ite_eq_right (fun hh => hi (hφ hh))
  · simp

lemma letterLift_injective {n d D : ℕ} (φ : Fin d → Fin D) (hφ : Function.Injective φ) :
    Function.Injective (letterLift (n := n) φ) := by
  intro x y hxy
  funext w
  have hh := congrFun hxy (φ ∘ w)
  simpa only [letterLift_eval φ hφ] using hh

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_ShapeRigidity
attribute [-simp] _root_.OAI.Saxl.tableauInclusion_cell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uX uV uW

namespace Saxl

lemma tableau_image {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    Finset.univ.image (fun i : Fin n => (t i).val) = μ.cells := by
  classical
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩; exact (t i).property
  · intro hx; exact ⟨t.symm ⟨x, hx⟩, by simp⟩

lemma tableau_sum {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) (f : ℕ × ℕ → ℤ) :
    ∑ i, f (t i).val = ∑ c ∈ μ.cells, f c := by
  classical
  conv_rhs => rw [← tableau_image t]
  rw [Finset.sum_image]
  intro i hi j hj h
  exact t.injective (Subtype.val_injective h)

/- Zero-based row-index statistic of a partition. -/

lemma mixed_moment_le {n : ℕ} {μ ν : YoungDiagram}
    (t : Tableau n μ) (u : Tableau n ν) (g : Equiv.Perm (Fin n))
    (hi : Function.Injective (fun i => ((u (g i)).val.1, (t i).val.2))) :
    rowMoment μ ≤ rowMoment ν := by
  classical
  let f : Fin n → ℕ × ℕ := fun i => ((u (g i)).val.1, (t i).val.2)
  let w : ℕ × ℕ → ℤ := fun c => 2 * (μ.colLen c.2 : ℤ) - 2 * c.1 - 1
  have h := finset_signed_sum_le (Finset.univ.image f) μ.cells w
    (fun c hc => by have hh := YoungDiagram.mem_iff_lt_colLen.mp hc; dsimp [w]; omega)
    (fun c hc => by
      have hh : μ.colLen c.2 ≤ c.1 :=
        le_of_not_gt (fun h => hc (YoungDiagram.mem_iff_lt_colLen.mpr h))
      dsimp [w]; omega)
  rw [Finset.sum_image (fun _ _ _ _ h => hi h), ← tableau_sum t w] at h
  simp only [w, Finset.sum_sub_distrib, ← Finset.mul_sum] at h
  rw [Equiv.sum_comp g (fun i => ((u i).val.1 : ℤ))] at h
  have ht := tableau_sum t (fun c => (c.1 : ℤ))
  have hu := tableau_sum u (fun c => (c.1 : ℤ))
  change _ = rowMoment μ at ht
  change _ = rowMoment ν at hu
  omega

lemma mixed_support_eq {n : ℕ} {μ ν : YoungDiagram}
    (t : Tableau n μ) (u : Tableau n ν) (g : Equiv.Perm (Fin n))
    (hi : Function.Injective (fun i => ((u (g i)).val.1, (t i).val.2)))
    (hm : rowMoment μ = rowMoment ν) :
    Finset.univ.image (fun i => ((u (g i)).val.1, (t i).val.2)) = μ.cells := by
  classical
  let f : Fin n → ℕ × ℕ := fun i => ((u (g i)).val.1, (t i).val.2)
  let w : ℕ × ℕ → ℤ := fun c => 2 * (μ.colLen c.2 : ℤ) - 2 * c.1 - 1
  apply finset_eq_of_signed_sum _ _ w
    (fun c hc => by have hh := YoungDiagram.mem_iff_lt_colLen.mp hc; dsimp [w]; omega)
    (fun c hc => by
      have hh : μ.colLen c.2 ≤ c.1 :=
        le_of_not_gt (fun h => hc (YoungDiagram.mem_iff_lt_colLen.mpr h))
      dsimp [w]; omega)
  rw [Finset.sum_image (fun _ _ _ _ h => hi h), ← tableau_sum t w]
  simp only [w, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [Equiv.sum_comp g (fun i => ((u i).val.1 : ℤ))]
  have ht := tableau_sum t (fun c => (c.1 : ℤ))
  have hu := tableau_sum u (fun c => (c.1 : ℤ))
  change _ = rowMoment μ at ht
  change _ = rowMoment ν at hu
  rw [ht, hu, hm]

lemma rowLen_eq_count {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) (r : ℕ) :
    μ.rowLen r = (Finset.univ.filter (fun i => (t i).val.1 = r)).card := by
  classical
  rw [YoungDiagram.rowLen_eq_card]
  have hf : μ.row r = (Finset.univ.filter (fun i => (t i).val.1 = r)).image
      (fun i => (t i).val) := by
    unfold YoungDiagram.row
    conv_lhs => rw [← tableau_image t]
    rw [Finset.filter_image]
  rw [hf, Finset.card_image_iff.mpr]
  intro i hi j hj h
  exact t.injective (Subtype.val_injective h)

lemma shapes_eq_of_mixed {n : ℕ} {μ ν : YoungDiagram}
    (t : Tableau n μ) (u : Tableau n ν) (g : Equiv.Perm (Fin n))
    (hi : Function.Injective (fun i => ((u (g i)).val.1, (t i).val.2)))
    (hm : rowMoment μ = rowMoment ν) : μ = ν := by
  classical
  have hs := mixed_support_eq t u g hi hm
  have hrow : ∀ r, μ.rowLen r = ν.rowLen r := by
    intro r
    rw [YoungDiagram.rowLen_eq_card, YoungDiagram.row, ← hs,
      Finset.filter_image, Finset.card_image_iff.mpr (fun i _ j _ h => hi h),
      rowLen_eq_count u r]
    apply Finset.card_equiv g
    intro i
    simp
  apply YoungDiagram.ext
  ext c
  rcases c with ⟨r, s⟩
  change (r, s) ∈ μ ↔ (r, s) ∈ ν
  simp only [YoungDiagram.mem_iff_lt_rowLen, hrow]

lemma columnAlt_polytabloid_ne_zero {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    columnAlt t (polytabloid t) ≠ 0 := by
  intro hz
  have h := congrFun hz (rowWord t)
  rw [columnAlt_coefficient] at h
  change dotProduct (polytabloid t) (polytabloid t) = 0 at h
  conv at h => lhs; rhs; rw [← polytabloid_real t]
  let : PartialOrder ℂ := RCLike.toPartialOrder
  let : StarOrderedRing ℂ := RCLike.toStarOrderedRing
  exact polytabloid_ne_zero t (dotProduct_self_star_eq_zero.mp h)

lemma mixed_injective_of_columnAlt_ne_zero {n : ℕ} {μ ν : YoungDiagram}
    (t : Tableau n μ) (u : Tableau n ν)
    {x : WordSpace n (ν.colLen 0)} (hx : x ∈ tabloidSub u)
    (hz : columnAlt t x ≠ 0) :
    ∃ g : Equiv.Perm (Fin n),
      Function.Injective (fun i => ((u (g i)).val.1, (t i).val.2)) := by
  classical
  by_contra h
  push Not at h
  have hall : ∀ g : Equiv.Perm (Fin n),
      columnAlt t (wordRep n (ν.colLen 0) g (Pi.single (rowWord u) 1)) = 0 := by
    intro g
    have hh := h g⁻¹
    simp only [Function.Injective] at hh
    push Not at hh
    obtain ⟨i, j, he, hij⟩ := hh
    rw [wordRep_single]
    exact columnAlt_collision t _ i j hij (Prod.mk.inj he).2
      (Fin.ext (Prod.mk.inj he).1)
  apply hz
  clear hz
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨g, rfl⟩ := hy; exact hall g
  | zero => exact map_zero _
  | add y z hy hz ihy ihz => rw [map_add, ihy, ihz, add_zero]
  | smul c y hy ih => rw [map_smul, ih, smul_zero]

/- The column operator on any genuine representation of the same group. -/
def columnOperator {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) : Module.End ℂ V := by
  classical
  letI := Fintype.ofFinite (columnGroup t)
  exact ∑ g : columnGroup t, signC (g : Equiv.Perm (Fin n)) • ρ g

lemma columnOperator_intertwining {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (Equiv.Perm (Fin n)) V}
    {σ : Representation ℂ (Equiv.Perm (Fin n)) W}
    (f : Representation.IntertwiningMap ρ σ) (x : V) :
    f (columnOperator t ρ x) = columnOperator t σ (f x) := by
  classical
  simp only [columnOperator, LinearMap.sum_apply, LinearMap.smul_apply,
    map_sum, map_smul, Representation.IntertwiningMap.isIntertwining]

lemma columnOperator_subtype {n d : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (S : Subrepresentation (wordRep n d)) (x : S.toSubmodule) :
    (columnOperator t S.toRepresentation x).val = columnAlt t x.val := by
  let inc : Representation.IntertwiningMap S.toRepresentation (wordRep n d) :=
    { toLinearMap := S.toSubmodule.subtype
      isIntertwining' := fun g => rfl }
  exact columnOperator_intertwining t inc x

lemma mixed_injective_of_equiv {n : ℕ} {μ ν : YoungDiagram}
    (t : Tableau n μ) (u : Tableau n ν)
    (e : Representation.Equiv (spechtRep t) (spechtRep u)) :
    ∃ g : Equiv.Perm (Fin n),
      Function.Injective (fun i => ((u (g i)).val.1, (t i).val.2)) := by
  let p : Specht t := ⟨polytabloid t, mem_cyclic _ _⟩
  apply mixed_injective_of_columnAlt_ne_zero t u
    (spechtSub_le_tabloidSub u (e p).property)
  intro hz
  have he := columnOperator_intertwining t e.toIntertwiningMap p
  have hy : columnOperator t (spechtRep u) (e p) = 0 := by
    apply Subtype.ext
    exact (columnOperator_subtype t (spechtSub u) (e p)).trans hz
  change e (columnOperator t (spechtRep t) p) = columnOperator t (spechtRep u) (e p) at he
  rw [hy] at he
  have ht : columnOperator t (spechtRep t) p = 0 := e.injective (he.trans (map_zero e).symm)
  have hh := congrArg Subtype.val ht
  exact columnAlt_polytabloid_ne_zero t
    ((columnOperator_subtype t (spechtSub t) p).symm.trans hh)

/- Distinct genuine complex Specht shapes are inequivalent. -/
theorem specht_shape_rigidity {n : ℕ} {μ ν : YoungDiagram}
    (t : Tableau n μ) (u : Tableau n ν)
    (e : Representation.Equiv (spechtRep t) (spechtRep u)) : μ = ν := by
  obtain ⟨g, hg⟩ := mixed_injective_of_equiv t u e
  obtain ⟨h, hh⟩ := mixed_injective_of_equiv u t e.symm
  exact shapes_eq_of_mixed t u g hg
    (le_antisymm (mixed_moment_le t u g hg) (mixed_moment_le u t h hh))

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_SpechtClassification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uV uG

namespace Saxl

/- Rows enumerate exactly the actual cells, including the empty diagram. -/

def partitionTableau {n : ℕ} (p : Nat.Partition n) : Tableau n (partitionDiagram p) :=
  canonicalTableau _ (partitionDiagram_card p)

/- Cycle-type partition, with only the definitional `card (Fin n)=n` transport. -/
def spechtCharacter {n : ℕ} (p : Nat.Partition n) : classFunctions n :=
  ⟨(spechtRep (partitionTableau p)).character, char_mem_classFunctions _⟩

/- Bilinear character scalar product used by the finite-group orthogonality theorem. -/

lemma spechtCharacter_orthonormal {n : ℕ} (p q : Nat.Partition n) :
    charFunctional (spechtCharacter q).val (spechtCharacter p).val = if p = q then 1 else 0 := by
  classical
  let : Invertible (Nat.card (Equiv.Perm (Fin n)) : ℂ) :=
    invertibleOfNonzero (complex_card_ne_zero _)
  let := specht_irreducible (partitionTableau p)
  let := specht_irreducible (partitionTableau q)
  have h := Representation.char_orthonormal (spechtRep (partitionTableau p))
    (spechtRep (partitionTableau q))
  change _ = _ at h
  have he : Nonempty ((spechtRep (partitionTableau q)).Equiv
      (spechtRep (partitionTableau p))) ↔ p = q := by
    constructor
    · rintro ⟨e⟩
      exact (partitionDiagram_injective
        (specht_shape_rigidity (partitionTableau q) (partitionTableau p) e)).symm
    · rintro rfl
      exact ⟨Representation.Equiv.refl _⟩
  simpa only [he, charFunctional, spechtCharacter, LinearMap.coe_mk, AddHom.coe_mk] using h

lemma spechtCharacter_linearIndependent (n : ℕ) :
    LinearIndependent ℂ (spechtCharacter (n := n)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc p
  have h := congrArg (fun f : classFunctions n => charFunctional (spechtCharacter p).val f.val) hc
  change charFunctional (spechtCharacter p).val
    ((classFunctions n).subtype (∑ i, c i • spechtCharacter i)) =
    charFunctional (spechtCharacter p).val ((classFunctions n).subtype 0) at h
  simp only [map_sum, map_smul, map_zero] at h
  change (∑ i, c i * charFunctional (spechtCharacter p).val (spechtCharacter i).val) = 0 at h
  simp_rw [spechtCharacter_orthonormal] at h
  simpa using h

lemma spechtCharacter_span (n : ℕ) :
    Submodule.span ℂ (Set.range (spechtCharacter (n := n))) = ⊤ := by
  apply (spechtCharacter_linearIndependent n).span_eq_top_of_card_eq_finrank'
  exact le_antisymm (spechtCharacter_linearIndependent n).fintype_card_le_finrank
    (classFunctions_finrank_le n)



theorem irreducible_equiv_specht {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    [Module.Finite ℂ V] (ρ : Representation ℂ (Equiv.Perm (Fin n)) V)
    [Representation.IsIrreducible ρ] :
    ∃ p : Nat.Partition n, Nonempty (ρ.Equiv (spechtRep (partitionTableau p))) := by
  classical
  let : Invertible (Nat.card (Equiv.Perm (Fin n)) : ℂ) :=
    invertibleOfNonzero (complex_card_ne_zero _)
  by_contra h
  push Not at h
  let f : (classFunctions n) →ₗ[ℂ] ℂ :=
    (charFunctional ρ.character).comp (classFunctions n).subtype
  have hf : ∀ p : Nat.Partition n, f (spechtCharacter p) = 0 := by
    intro p
    let := specht_irreducible (partitionTableau p)
    have hp := Representation.char_orthonormal (spechtRep (partitionTableau p)) ρ
    rw [ite_eq_right (fun he => (h p).false he.some)] at hp
    exact hp
  have hk : Submodule.span ℂ (Set.range (spechtCharacter (n := n))) ≤ LinearMap.ker f := by
    rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    exact hf p
  rw [spechtCharacter_span] at hk
  have hz := hk (show (⟨ρ.character, char_mem_classFunctions ρ⟩ : classFunctions n) ∈ ⊤ from trivial)
  change charFunctional ρ.character ρ.character = 0 at hz
  have hone := Representation.char_orthonormal ρ ρ
  rw [ite_eq_left ⟨Representation.Equiv.refl ρ⟩] at hone
  exact one_ne_zero (hone.symm.trans hz)



end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_SupportSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uR uX uY uG uV

namespace Saxl
open scoped MonoidAlgebra

theorem intertwining_separates_of_simple_support {G : Type uG} {X : Type uX} {Y : Type uY}
    [Group G] [Finite G] [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y]
    (ρ : Representation ℂ G X) (σ : Representation ℂ G Y)
    (h : ∀ S : Subrepresentation ρ, Representation.IsIrreducible S.toRepresentation →
      ∃ f : Representation.IntertwiningMap S.toRepresentation σ, f ≠ 0)
    (x : X) (hx : x ≠ 0) :
    ∃ f : Representation.IntertwiningMap ρ σ, f x ≠ 0 := by
  classical
  have hs (S : Submodule ℂ[G] ρ.asModule) (hS : IsSimpleModule ℂ[G] S) :
      ∃ f : S →ₗ[ℂ[G]] σ.asModule, f ≠ 0 := by
    let P := Subrepresentation.ofSubmodule' S
    let := hS
    obtain ⟨f, hf⟩ := h P (subrep_irreducible_of_simple S)
    let F := Representation.IntertwiningMap.equivLinearMapAsModule _ _ f
    let E : P.toRepresentation.asModule ≃ₗ[ℂ[G]] S := subrepModuleEquiv P
    refine ⟨F.comp E.symm.toLinearMap, ?_⟩
    intro hz
    apply hf
    apply (Representation.IntertwiningMap.equivLinearMapAsModule _ _).injective
    ext v
    have he := LinearMap.congr_fun hz (E v)
    change F v = 0
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      E.symm_apply_apply, LinearMap.zero_apply] using he
  obtain ⟨f, hf⟩ := hom_separates_of_simple_support hs (ρ.asModuleEquiv.symm x)
    (fun he => hx (ρ.asModuleEquiv.symm.injective (he.trans (map_zero _).symm)))
  exact ⟨(Representation.IntertwiningMap.equivLinearMapAsModule _ _).symm f, hf⟩

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_BandOrbit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uX uY

namespace Saxl

def bandOrbitMap {n a b k : ℕ} {X : Type uX} {Y : Type uY}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (e : Fin n ≃ Fin a ⊕ Fin b) (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    (c : Fin b → Fin k) (F : X →ₗ[ℂ] Y) :
    X →ₗ[ℂ] ((Fin b → Fin k) → Y) where
  toFun x w := ∑ g : Equiv.Perm (Fin b),
    ((Pi.single (c ∘ (g⁻¹ : Equiv.Perm (Fin b))) (1:ℂ) : WordSpace b k) w) • F (ρ (sumPerm e 1 g⁻¹) x)
  map_add' x y := by ext w; simp only [map_add,smul_add,Finset.sum_add_distrib,Pi.add_apply]
  map_smul' c x := by
    ext w
    simp only [map_smul,Pi.smul_apply,Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro g hg
    exact smul_comm _ _ _

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_BandGlue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uX

namespace Saxl

/- Apply a band intertwiner to every scalar high-coordinate of a colored
strip orbit map. This is the concrete tensor product of the two maps. -/
def bandGlue {n a b k d : ℕ} {X : Type uX} [AddCommGroup X] [Module ℂ X]
    (e : Fin n ≃ Fin a ⊕ Fin b)
    (T : X →ₗ[ℂ] ((Fin b → Fin k) → WordSpace a d))
    (L : WordSpace b k →ₗ[ℂ] WordSpace b d) : X →ₗ[ℂ] WordSpace n d where
  toFun x w := L (fun cb => T x cb (leftWord e w)) (rightWord e w)
  map_add' x y := by
    ext w
    simp only [map_add, Pi.add_apply]
    change L ((fun cb => T x cb (leftWord e w)) + (fun cb => T y cb (leftWord e w))) (rightWord e w) = _
    rw [map_add]
    rfl
  map_smul' c x := by
    ext w
    simp only [map_smul, Pi.smul_apply, RingHom.id_apply]
    change L (c • (fun cb => T x cb (leftWord e w))) (rightWord e w) = _
    rw [map_smul]
    rfl


def coordinateSub (n d : ℕ) (P : (Fin n → Fin d) → Prop) : Submodule ℂ (WordSpace n d) where
  carrier := {x | ∀ w, ¬ P w → x w = 0}
  zero_mem' := by intro w hw; rfl
  add_mem' := by intro x y hx hy w hw; change x w+y w=0; rw [hx w hw,hy w hw,add_zero]
  smul_mem' := by intro c x hx w hw; change c*x w=0; rw [hx w hw,mul_zero]

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_SignEquivalence
attribute [-simp] _root_.OAI.Saxl.tableauInclusion_cell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uV

namespace Saxl

def transposeTableau {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    Tableau n μ.transpose := t.trans
  { toFun := fun c => ⟨c.val.swap, YoungDiagram.mem_transpose.mpr (by simp)⟩
    invFun := fun c => ⟨c.val.swap, YoungDiagram.mem_transpose.mp c.property⟩
    left_inv := by intro c; apply Subtype.ext; exact Prod.swap_swap _
    right_inv := by intro c; apply Subtype.ext; exact Prod.swap_swap _ }

/- Twisting by the actual sign character, on the same complex vector space. -/
def signTwist {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) :
    Representation ℂ (Equiv.Perm (Fin n)) V where
  toFun g := signC g • ρ g
  map_one' := by simp
  map_mul' g h := by ext x; simp [map_mul, smul_smul, mul_comm]

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_CyclicTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uG uX uY

namespace Saxl

def CyclicSaxlConjecture : Prop :=
  ∀ m, 1 ≤ m → ∀ (μ : YoungDiagram) (hμ : μ.card = (staircase m).card),
    ∃ f : Representation.IntertwiningMap (spechtRep (canonicalTableau μ hμ))
      (staircaseCyclic m).toRepresentation, f ≠ 0

/- A proof of cyclic support proves the original Kronecker-multiplicity target. -/

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_RepeatedProjection
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.relabelWord_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uX

namespace Saxl
/- Coordinate projection; equivariance is asserted only for preserved predicates. -/

def orbitProjection {n d : ℕ} (t : Fin n → Fin d) :
    Representation.IntertwiningMap (wordRep n d) (wordRep n d) where
  toLinearMap := coordinateProjection (wordOrbit t)
  isIntertwining' g := by
    classical
    apply LinearMap.ext
    intro x
    ext c
    change (if wordOrbit t c then x (c ∘ g) else 0) =
      (if wordOrbit t (c ∘ g) then x (c ∘ g) else 0)
    rw [wordOrbit_perm]

def pairSumMap (n d e : ℕ) :
    Representation.IntertwiningMap (wordRep n (d*d)) (wordRep n e) :=
  wordMap (fun a c => if (finProdFinEquiv.symm a).1.val +
    (finProdFinEquiv.symm a).2.val = c.val then 1 else 0)

lemma wordTensor_single {n d e : ℕ} (a : Fin n → Fin d) (b : Fin n → Fin e) :
    wordTensor n d e (Pi.single a 1 ⊗ₜ[ℂ] Pi.single b 1) = Pi.single (mergeWords a b) 1 := by
  classical
  ext c
  rw [wordTensor_tmul]
  by_cases h : c = mergeWords a b
  · subst c; simp
  · have hh : splitLeft c ≠ a ∨ splitRight c ≠ b := by
      by_contra hn
      push Not at hn
      exact h (by rw [← merge_split c, hn.1, hn.2])
    rcases hh with hl | hr
    · simp [Pi.single_apply, h, hl]
    · simp [Pi.single_apply, h, hr]

lemma pairSumMap_single {n d e : ℕ} (a b : Fin n → Fin d) (c : Fin n → Fin e) :
    pairSumMap n d e (Pi.single (mergeWords a b) 1) c =
      if ∀ i, (a i).val + (b i).val = (c i).val then 1 else 0 := by
  classical
  rw [pairSumMap, wordMap_single]
  simp only [mergeWords, Equiv.symm_apply_apply]
  by_cases h : ∀ i, (a i).val + (b i).val = (c i).val
  · simp [h]
  · rw [ite_eq_right h]
    push Not at h
    obtain ⟨i, hi⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

lemma altWord_inverse_sum {n d : ℕ} (H : Subgroup (Equiv.Perm (Fin n)))
    (a : Fin n → Fin d) :
    letI := Fintype.ofFinite H
    altWord H a = ∑ g : H, signC (g : Equiv.Perm (Fin n)) • Pi.single (a ∘ (g : Equiv.Perm (Fin n))) 1 := by
  classical
  let := Fintype.ofFinite H
  unfold altWord
  simp_rw [wordRep_single]
  apply Eq.trans ?_ (Equiv.sum_comp (Equiv.inv H) _)
  apply Finset.sum_congr rfl
  intro g hg
  congr 1
  exact (signC_inv g.val).symm


end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_StaircaseSign
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uX uY uZ

namespace Saxl

def repeatedTarget (m : ℕ) : Fin (staircase m).card → Fin ((staircase m).colLen 0) :=
  fun i => Fin.rev (rowWord (stairTableau m) i)

def signTwistMap {n : ℕ} {X : Type uX} {Y : Type uY} [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y]
    {ρ : Representation ℂ (Equiv.Perm (Fin n)) X} {σ : Representation ℂ (Equiv.Perm (Fin n)) Y}
    (f : Representation.IntertwiningMap ρ σ) :
    Representation.IntertwiningMap (signTwist ρ) (signTwist σ) where
  toLinearMap := f.toLinearMap
  isIntertwining' g := by
    ext x
    change f (signC g • ρ g x) = signC g • σ g (f x)
    rw [map_smul, f.isIntertwining]

/- A sign intertwiner in the second factor twists the diagonal product. -/
def tensorAnti {n : ℕ} {X : Type uX} {Y : Type uY} {Z : Type uZ} [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] [AddCommGroup Z] [Module ℂ Z]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    {σ : Representation ℂ (Equiv.Perm (Fin n)) Y} {τ : Representation ℂ (Equiv.Perm (Fin n)) Z}
    (f : Representation.IntertwiningMap σ (signTwist τ)) :
    Representation.IntertwiningMap (signTwist (ρ.tprod σ)) (ρ.tprod τ) where
  toLinearMap := TensorProduct.map LinearMap.id f.toLinearMap
  isIntertwining' g := by
    ext x y
    change TensorProduct.map LinearMap.id f.toLinearMap
      (signC g • (ρ g x ⊗ₜ[ℂ] σ g y)) = ρ g x ⊗ₜ[ℂ] τ g (f y)
    rw [map_smul, TensorProduct.map_tmul]
    change signC g • (ρ g x ⊗ₜ[ℂ] f (σ g y)) = _
    rw [f.isIntertwining]
    change signC g • (ρ g x ⊗ₜ[ℂ] (signC g • τ g (f y))) = _
    rw [TensorProduct.tmul_smul, smul_smul, signC_mul_self, one_smul]

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_DominatedQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

def wordTensorEquiv (n d e : ℕ) :
    ((wordRep n d).tprod (wordRep n e)).Equiv (wordRep n (d*e)) where
  toLinearEquiv := wordTensor n d e
  isIntertwining' g := by
    apply LinearMap.ext
    intro z
    exact wordTensor_equivariant g z

def ambientSignMap (m : ℕ)
    (φ : (spechtRep (stairTableau m)).Equiv (signTwist (spechtRep (stairRowTableau m)))) :
    Representation.IntertwiningMap (wordRep (staircase m).card ((staircase m).colLen 0))
      (signTwist (wordRep (staircase m).card ((staircase m).colLen 0))) :=
  (signTwistMap (spechtInclusion (stairRowTableau m))).comp
    (φ.toIntertwiningMap.comp (subrepProject (spechtSub (stairTableau m))
      (fun _ hx => cyclic_star _ (polytabloid_real _) hx)))

def pairAntiMap (m : ℕ)
    (φ : (spechtRep (stairTableau m)).Equiv (signTwist (spechtRep (stairRowTableau m)))) :
    Representation.IntertwiningMap
      (signTwist (wordRep (staircase m).card ((staircase m).colLen 0 * (staircase m).colLen 0)))
      (wordRep (staircase m).card ((staircase m).colLen 0 * (staircase m).colLen 0)) :=
  (wordTensorEquiv _ _ _).toIntertwiningMap.comp
    ((tensorAnti (wordRep _ _) (ambientSignMap m φ)).comp
      (signTwistMap (wordTensorEquiv _ _ _).symm.toIntertwiningMap))

def dominatedQuotient (m : ℕ)
    (φ : (spechtRep (stairTableau m)).Equiv (signTwist (spechtRep (stairRowTableau m)))) :
    Representation.IntertwiningMap (signTwist (staircaseCyclic m).toRepresentation)
      (wordRep (staircase m).card ((staircase m).colLen 0)) :=
  (orbitProjection (repeatedTarget m)).comp ((pairSumMap _ _ _).comp
    ((pairAntiMap m φ).comp (signTwistMap
      { toLinearMap := (staircaseCyclic m).toSubmodule.subtype
        isIntertwining' := fun _ => rfl })))

/- The exact staircase permutation generator occurs in the image of the
sign-twisted cyclic staircase module, with no Young-rule input. -/

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_DominatedSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uX uY

namespace Saxl

lemma rowWord_content {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (j : Fin (μ.colLen 0)) :
    (Finset.univ.filter (fun i => rowWord t i = j)).card = μ.rowLen j := by
  classical
  let e : {i // rowWord t i = j} ≃ Fin (μ.rowLen j) :=
    { toFun := fun i => ⟨(t i.val).val.2, by
        have hh := YoungDiagram.mem_iff_lt_rowLen.mp (t i.val).property
        have hj := congrArg Fin.val i.property
        change (t i.val).val.1 = j.val at hj
        simpa only [hj] using hh⟩
      invFun := fun k => ⟨t.symm ⟨(j.val,k.val), YoungDiagram.mem_iff_lt_rowLen.mpr k.isLt⟩,
        by apply Fin.ext; change (t (t.symm _)).val.1 = _; simp only [Equiv.apply_symm_apply]⟩
      left_inv := by
        intro i
        apply Subtype.ext
        apply t.injective
        simp only [Equiv.apply_symm_apply]
        apply Subtype.ext
        apply Prod.ext
        · exact (congrArg Fin.val i.property).symm
        · rfl
      right_inv := by intro k; apply Fin.ext; simp only [Equiv.apply_symm_apply] }
  simpa only [Fintype.card_subtype, Fintype.card_fin] using Fintype.card_congr e

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Band_OddPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Odd Path. -/

section

noncomputable section

namespace Saxl.Columns

def dualBlockWord (rs : List ℕ) (N : ℕ → Band.Mat) : WordSpace rs.sum 4 :=
  ∑ π : Perms rs, sg π • Path.pureWord
    (fun q => N (row (perm π (enumerate rs q))))

end Saxl.Columns
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_ColumnReorder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Column Reorder. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl.Columns

theorem columns_equiv_of_perm {rs ss : List ℕ} (h : rs.Perm ss) :
    ∃ e : Cells rs ≃ Cells ss,
      (∀ c, row (e c) = row c) ∧
      (∀ c d, col (e c) = col (e d) ↔ col c = col d) := by
  induction h with
  | nil =>
    exact ⟨Equiv.refl _, fun c => isEmptyElim c, fun c => isEmptyElim c⟩
  | @cons r rs ss h ih =>
    obtain ⟨e,hr,hc⟩ := ih
    refine ⟨(Equiv.refl (Fin r)).sumCongr e, ?_, ?_⟩
    · intro c
      rcases c with c | c
      · rfl
      · exact hr c
    · intro c d
      rcases c with c | c <;> rcases d with d | d
      · simp [col]
      · simp [col]
      · simp [col]
      · simpa only [Equiv.sumCongr_apply, Sum.map_inr, col, Nat.add_right_cancel_iff] using hc c d
  | swap r s rs =>
    let e : Cells (s::r::rs) ≃ Cells (r::s::rs) :=
      (Equiv.sumAssoc (Fin s) (Fin r) (Cells rs)).symm.trans
        (((Equiv.sumComm (Fin s) (Fin r)).sumCongr (Equiv.refl (Cells rs))).trans
          (Equiv.sumAssoc (Fin r) (Fin s) (Cells rs)))
    refine ⟨e, ?_, ?_⟩
    · intro c
      rcases c with c | (c | c) <;> rfl
    · intro c d
      rcases c with c | (c | c) <;> rcases d with d | (d | d) <;>
        simp [e, col]
  | @trans rs ss ts h h' ih ih' =>
    obtain ⟨e,hr,hc⟩ := ih
    obtain ⟨f,hr',hc'⟩ := ih'
    refine ⟨e.trans f, ?_, ?_⟩
    · intro c
      exact (hr' (e c)).trans (hr c)
    · intro c d
      exact (hc' (e c) (e d)).trans (hc c d)

theorem place_columns {rs : List ℕ} (μ : YoungDiagram)
    (h : rs.Perm μ.transpose.rowLens) :
    ∃ e : Cells rs ≃ μ.cells,
      (∀ c, (e c).val.1 = row c) ∧
      (∀ c d, (e c).val.2 = (e d).val.2 ↔ col c = col d) := by
  obtain ⟨e,hr,hc⟩ := columns_equiv_of_perm h
  exact ⟨e.trans (toYoung μ), hr, hc⟩

def listColumnPerm (rs : List ℕ) (π : Perms rs) :
    fiberGroup (fun i : Fin rs.sum => col (enumerate rs i)) :=
  ⟨(enumerate rs).symm.permCongr (perm π), by
    intro i
    simp only [Equiv.permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
    exact perm_col π _⟩

lemma listColumnPerm_bijective (rs : List ℕ) : Function.Bijective (listColumnPerm rs) := by
  constructor
  · intro π σ h
    apply perm_injective rs
    apply (enumerate rs).symm.permCongr.injective
    exact congrArg Subtype.val h
  · intro g
    let e := enumerate rs
    obtain ⟨π,hπ⟩ := perm_surjective rs (e.permCongr g.val) (by
      intro c
      have hh := g.property (e.symm c)
      simpa only [Equiv.permCongr_apply, e, Equiv.apply_symm_apply] using hh)
    refine ⟨π, ?_⟩
    apply Subtype.ext
    change e.symm.permCongr (perm π) = g.val
    rw [hπ]
    apply Equiv.ext
    intro i
    simp [Equiv.permCongr_apply]

lemma listColumnPerm_sign (rs : List ℕ) (π : Perms rs) :
    signC (listColumnPerm rs π).val = sg π := by
  change (((Equiv.Perm.sign ((enumerate rs).symm.permCongr (perm π)) : ℤ) : ℂ)) = sg π
  rw [Equiv.Perm.sign_permCongr]
  exact sign_perm π

def columnWedge (r : ℕ) (N : ℕ → Band.Mat) : WordSpace r 4 :=
  ∑ π : Equiv.Perm (Fin r), (((Equiv.Perm.sign π : ℤ) : ℂ)) •
    Path.pureWord (fun i => N (π i).val)

end Saxl.Columns
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_RepeatedColumns
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.relabelWord_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Repeated Columns. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

lemma paired_term_projection_free {n d e : ℕ} (H : Subgroup (Equiv.Perm (Fin n)))
    (a : Fin n → Fin d) (t : Fin n → Fin e) (ω : H)
    (ht : ∀ g : H, ∀ i, t (g.val i) = t i)
    (ha : ∀ g h : H, a ∘ g.val = a ∘ h.val → g = h)
    (hω : ∀ i, (a i).val + (a (ω.val i)).val = (t i).val) (g h : H) :
    orbitProjection t (pairSumMap n d e (Pi.single
      (mergeWords (a ∘ g.val) (a ∘ h.val)) 1)) =
      if h = ω*g then Pi.single t 1 else 0 := by
  classical
  ext c
  change (if wordOrbit t c then pairSumMap n d e (Pi.single
      (mergeWords (a ∘ g.val) (a ∘ h.val)) 1) c else 0) = _
  rw [pairSumMap_single]
  simp only [Function.comp_apply]
  by_cases he : h = ω*g
  · rw [ite_eq_left he]
    have hr := (paired_relation_iff_free H a t ω ht ha hω g h).mpr he
    by_cases hc : c = t
    · subst c
      rw [ite_eq_left ⟨1, rfl⟩, ite_eq_left hr]
      simp
    · rw [Pi.single_eq_of_ne hc]
      have hn : ¬ ∀ i, (a (g.val i)).val + (a (h.val i)).val = (c i).val := by
        intro hh
        apply hc
        funext i
        exact Fin.ext ((hh i).symm.trans (hr i))
      simp only [hn, ite_false, if_false, ite_self]
  · rw [ite_eq_right he]
    change (if wordOrbit t c then _ else _) = (0:ℂ)
    by_cases ho : wordOrbit t c
    · rw [ite_eq_left ho]
      apply ite_eq_right
      intro hh
      obtain ⟨k,hk⟩ := ho
      have heq : (fun i => ((c i).val : ℝ)) = fun i => ((t i).val : ℝ) := by
        apply pair_sum_rigidity (fun i => ((a i).val : ℝ)) (fun i => ((t i).val : ℝ))
          (fun i => ((c i).val : ℝ)) ω.val g.val h.val k
        · intro i; rw [ht ω i]
        · intro i; exact_mod_cast hω i
        · intro i; rw [ht g i]
        · intro i; rw [ht h i]
        · intro i; exact_mod_cast (hh i).symm
        · intro i; rw [hk]; rfl
      have hct : c = t := by
        funext i
        apply Fin.ext
        exact_mod_cast congrFun heq i
      rw [hct] at hh
      exact he ((paired_relation_iff_free H a t ω ht ha hω g h).mp hh)
    · rw [ite_eq_right ho]

theorem repeated_alt_projection_free {n d e : ℕ} (H : Subgroup (Equiv.Perm (Fin n)))
    (a : Fin n → Fin d) (t : Fin n → Fin e) (ω : H)
    (ht : ∀ g : H, ∀ i, t (g.val i) = t i)
    (ha : ∀ g h : H, a ∘ g.val = a ∘ h.val → g = h)
    (hω : ∀ i, (a i).val + (a (ω.val i)).val = (t i).val) :
    orbitProjection t (pairSumMap n d e (wordTensor n d d
      (altWord H a ⊗ₜ[ℂ] altWord H a))) =
      ((Nat.card H : ℂ) * signC ω.val) • Pi.single t 1 := by
  classical
  let := Fintype.ofFinite H
  rw [altWord_inverse_sum, TensorProduct.sum_tmul]
  simp only [TensorProduct.tmul_sum, map_sum, TensorProduct.smul_tmul_smul, map_smul,
    wordTensor_single, paired_term_projection_free H a t ω ht ha hω]
  simp only [smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
  have hs (g : H) : signC g.val * signC (ω*g).val = signC ω.val := by
    simp only [Subgroup.coe_mul, map_mul]
    calc
      signC g.val * (signC ω.val * signC g.val) = signC ω.val * (signC g.val * signC g.val) := by ring
      _ = signC ω.val := by rw [signC_mul_self, mul_one]
  simp only [hs, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, Fintype.card_eq_nat_card]

def columnReversal {n : ℕ} {α : YoungDiagram} (t : Tableau n α) : columnGroup t :=
  ⟨(t.trans (columnReversalEquiv α)).trans t.symm, by
    intro i
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
    rfl⟩

def columnLengthWord {n : ℕ} {α : YoungDiagram} (t : Tableau n α) :
    Fin n → Fin (α.colLen 0) := fun i =>
  ⟨α.colLen (t i).val.2 - 1, by
    have hx : (t i).val.1 < α.colLen (t i).val.2 :=
      YoungDiagram.mem_iff_lt_colLen.mp (t i).property
    have hy := α.colLen_anti 0 (t i).val.2 (Nat.zero_le _)
    omega⟩

lemma columnLengthWord_fixed {n : ℕ} {α : YoungDiagram} (t : Tableau n α)
    (g : columnGroup t) (i) : columnLengthWord t (g.val i) = columnLengthWord t i := by
  apply Fin.ext
  change α.colLen (t (g.val i)).val.2 - 1 = α.colLen (t i).val.2 - 1
  rw [g.property i]

lemma rowWord_column_free {n : ℕ} {α : YoungDiagram} (t : Tableau n α)
    (g h : columnGroup t) (he : rowWord t ∘ g.val = rowWord t ∘ h.val) : g = h := by
  apply Subtype.ext
  apply Equiv.ext
  intro i
  apply t.injective
  apply Subtype.ext
  exact Prod.ext (congrArg Fin.val (congrFun he i)) ((g.property i).trans (h.property i).symm)

lemma columnReversal_complement {n : ℕ} {α : YoungDiagram} (t : Tableau n α) (i) :
    (rowWord t i).val + (rowWord t ((columnReversal t).val i)).val =
      (columnLengthWord t i).val := by
  have hx : (t i).val.1 < α.colLen (t i).val.2 :=
      YoungDiagram.mem_iff_lt_colLen.mp (t i).property
  change (t i).val.1 + (t (t.symm (columnReversalCell α (t i)))).val.1 =
    α.colLen (t i).val.2 - 1
  rw [Equiv.apply_symm_apply]
  change (t i).val.1 + (α.colLen (t i).val.2 - 1 - (t i).val.1) =
    α.colLen (t i).val.2 - 1
  omega

theorem squared_polytabloid_projection {n : ℕ} {α : YoungDiagram} (t : Tableau n α) :
    orbitProjection (columnLengthWord t)
      (pairSumMap n (α.colLen 0) (α.colLen 0)
        (wordTensor n (α.colLen 0) (α.colLen 0) (polytabloid t ⊗ₜ[ℂ] polytabloid t))) =
      ((Nat.card (columnGroup t) : ℂ) * signC (columnReversal t).val) •
        Pi.single (columnLengthWord t) 1 := by
  simp only [polytabloid_eq_altWord]
  exact repeated_alt_projection_free (columnGroup t) (rowWord t) (columnLengthWord t)
    (columnReversal t) (columnLengthWord_fixed t) (rowWord_column_free t)
    (columnReversal_complement t)

lemma column_projection_coefficient_ne_zero {n : ℕ} {α : YoungDiagram} (t : Tableau n α) :
    (Nat.card (columnGroup t) : ℂ) * signC (columnReversal t).val ≠ 0 := by
  apply mul_ne_zero
  · exact Nat.cast_ne_zero.mpr (Nat.card_pos.ne')
  · intro hz
    have hh := signC_mul_self (columnReversal t).val
    rw [hz, zero_mul] at hh
    exact zero_ne_one hh

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_PolynomialDetection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial Detection. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

def jointContentWeight {n d e : ℕ}
    (F : Representation.IntertwiningMap (wordRep n d) (wordRep n e))
    (m : (Fin d × Fin e) →₀ ℕ) : ℂ :=
  if h : ∃ a b, jointContent a b = m then
    F (Pi.single h.choose 1) h.choose_spec.choose else 0

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_FlagColumns
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.relabelWord_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Flag Columns. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl.FlagColumns
open Columns

def pure {n d : ℕ} (N : Fin n → Fin d → ℂ) : WordSpace n d :=
  fun w => ∏ i, N i (w i)

def wedge (r : ℕ) {d : ℕ} (N : ℕ → Fin d → ℂ) : WordSpace r d :=
  ∑ π : Equiv.Perm (Fin r), signC π • pure (fun i => N (π i).val)

def blocks (rs : List ℕ) {d : ℕ} (N : ℕ → Fin d → ℂ) : WordSpace rs.sum d :=
  ∑ π : Perms rs, sg π • pure (fun i => N (row (perm π (enumerate rs i))))

lemma blocks_nil {d : ℕ} (N : ℕ → Fin d → ℂ) : blocks [] N = fun _ => 1 := by
  funext w
  change (∑ π : PUnit, (1 : ℂ) • pure (n := 0) (fun i => N (row (perm (rs := []) π (enumerate [] i)))) ) w = _
  simp only [Fintype.sum_unique, one_smul]
  simp [pure]

lemma blocks_cons (r : ℕ) (rs : List ℕ) {d : ℕ} (N : ℕ → Fin d → ℂ) :
    blocks (r::rs) N = positionProduct finSumFinEquiv.symm
      (wedge r N) (blocks rs N) := by
  classical
  funext w
  change (∑ π : Perms (r::rs), sg π • pure
    (fun q => N (row (perm π (enumerate (r::rs) q))))) w =
    wedge r N (leftWord finSumFinEquiv.symm w) *
      blocks rs N (rightWord finSumFinEquiv.symm w)
  simp only [Perms, Fintype.sum_prod_type, sg, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, wedge, blocks]
  change (∑ π, ∑ σ, ((Equiv.Perm.sign π : ℤ) : ℂ) * sg σ * _) =
    (∑ π : Equiv.Perm (Fin r), ((Equiv.Perm.sign π : ℤ) : ℂ) * _) * _
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro π hπ
  apply Finset.sum_congr rfl
  intro σ hσ
  have hp : pure (fun q => N (row (perm (rs := r::rs) (π,σ) (enumerate (r::rs) q)))) w =
      pure (fun q => N (π q).val) (leftWord finSumFinEquiv.symm w) *
        pure (fun q => N (row (perm σ (enumerate rs q))))
          (rightWord finSumFinEquiv.symm w) := by
    unfold pure
    change (∏ i : Fin (r + rs.sum), N (row (perm (rs := r::rs) (π, σ)
      (enumerate (r::rs) i))) (w i)) = _
    rw [Fin.prod_univ_add]
    congr 1
    · apply Finset.prod_congr rfl
      intro i hi
      erw [enumerate_left r rs i]
      rfl
    · apply Finset.prod_congr rfl
      intro i hi
      erw [enumerate_right r rs i]
      rfl
  rw [hp]
  ring

lemma mapped_placed {rs : List ℕ} {μ : YoungDiagram} {d : ℕ}
    (e : Cells rs ≃ μ.cells)
    (hr : ∀ c, (e c).val.1 = row c)
    (hc : ∀ c c', (e c).val.2 = (e c').val.2 ↔ col c = col c')
    (N : ℕ → Fin d → ℂ) :
    wordMap (fun (i : Fin (μ.colLen 0)) a => N i.val a)
      (polytabloid ((enumerate rs).trans e)) = blocks rs N := by
  classical
  have hg : columnGroup ((enumerate rs).trans e) =
      fiberGroup (fun i : Fin rs.sum => col (enumerate rs i)) := by
    apply Subgroup.ext
    intro g
    change (∀ i, (e (enumerate rs (g i))).val.2 = (e (enumerate rs i)).val.2) ↔ _
    simp only [hc]
    rfl
  let := Fintype.ofFinite (fiberGroup (fun i : Fin rs.sum => col (enumerate rs i)))
  rw [polytabloid_eq_altWord, hg, altWord_inverse_sum, map_sum]
  unfold blocks
  symm
  apply Fintype.sum_equiv (Equiv.ofBijective (listColumnPerm rs) (listColumnPerm_bijective rs))
  intro π
  simp only [Equiv.ofBijective_apply, map_smul]
  rw [listColumnPerm_sign]
  congr 1
  funext w
  rw [wordMap_single]
  unfold pure
  apply Finset.prod_congr rfl
  intro q hq
  apply congrArg (fun i => N i (w q))
  change row (perm π (enumerate rs q)) = (e (enumerate rs ((listColumnPerm rs π).val q))).val.1
  rw [hr]
  simp only [listColumnPerm, Equiv.permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply]

def tensorList {α : Type*} (k : α → ℕ) {d : ℕ}
    (v : ∀ a, WordSpace (k a) d) : (as : List α) → WordSpace (as.map k).sum d
  | [] => fun _ => 1
  | a::as => positionProduct finSumFinEquiv.symm (v a) (tensorList k v as)

end Saxl.FlagColumns
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_ZeroColumns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Zero Columns. -/

section

noncomputable section
namespace Saxl.Columns

theorem discard_zero_columns (rs : List ℕ) :
    ∃ e : Cells rs ≃ Cells (rs.filter (fun a => 0 < a)),
      (∀ c, row (e c) = row c) ∧
      (∀ c d, col (e c) = col (e d) ↔ col c = col d) := by
  induction rs with
  | nil => exact ⟨Equiv.refl _,fun c => isEmptyElim c,fun c => isEmptyElim c⟩
  | cons a rs ih =>
    obtain ⟨e,hr,hc⟩ := ih
    by_cases ha : 0 < a
    · rw [List.filter_cons_of_pos (by simpa using ha)]
      refine ⟨(Equiv.refl (Fin a)).sumCongr e, ?_, ?_⟩
      · intro c
        rcases c with c | c
        · rfl
        · exact hr c
      · intro c d
        rcases c with c | c <;> rcases d with d | d
        · simp [col]
        · simp [col]
        · simp [col]
        · simpa only [Equiv.sumCongr_apply, Sum.map_inr, col, Nat.add_right_cancel_iff]
            using hc c d
    · have ha0 : a = 0 := by omega
      subst a
      rw [List.filter_cons_of_neg (by simp)]
      refine ⟨(Equiv.emptySum (Fin 0) (Cells rs)).trans e, ?_, ?_⟩
      · intro c
        rcases c with c | c
        · exact Fin.elim0 c
        · exact hr c
      · intro c d
        rcases c with c | c
        · exact Fin.elim0 c
        · rcases d with d | d
          · exact Fin.elim0 d
          · change (col (e c) = col (e d) ↔ col c + 1 = col d + 1)
            simpa only [Nat.add_right_cancel_iff] using hc c d

theorem columnShape_placement (rs : List ℕ) :
    ∃ e : Cells rs ≃ (columnShape rs).cells,
      (∀ c, (e c).val.1 = row c) ∧
      (∀ c d, (e c).val.2 = (e d).val.2 ↔ col c = col d) := by
  obtain ⟨e,hr,hc⟩ := discard_zero_columns rs
  obtain ⟨f,hr',hc'⟩ := place_columns (columnShape rs)
    ((positiveSorted_perm rs).trans (by rw [columnShape_cols]))
  refine ⟨e.trans f,fun c => (hr' (e c)).trans (hr c),fun c d => ?_⟩
  exact (hc' (e c) (e d)).trans (hc c d)

lemma placed_card {rs : List ℕ} {μ : YoungDiagram} (e : Cells rs ≃ μ.cells) :
    μ.card = rs.sum := by
  have h := Fintype.card_congr ((enumerate rs).trans e)
  simpa only [Fintype.card_fin, Fintype.card_coe, YoungDiagram.card] using h.symm

lemma columnShape_card (rs : List ℕ) : (columnShape rs).card = rs.sum := by
  obtain ⟨e,_,_⟩ := columnShape_placement rs
  exact placed_card e

end Saxl.Columns
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_SymmetricPairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Symmetric Pairs. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

def symmetricPairs {n m : ℕ} (e : Fin n ≃ Fin m ⊕ Fin m) (d : ℕ) : WordSpace n d :=
  fun w => if leftWord e w = rightWord e w then 1 else 0

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_AlternateColumns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Alternate Columns. -/

section

noncomputable section
namespace Saxl

def alternateTableau {n a b : ℕ} (μ : YoungDiagram) (e : Fin n ≃ Fin a ⊕ Fin b)
    (s : Tableau a (ceilRows μ)) (t : Tableau b (halfRows μ)) : Tableau n μ :=
  e.trans ((Equiv.sumCongr s t).trans (alternateCells μ))

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_StandardColumns
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.relabelWord_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Standard Columns. -/

section

noncomputable section
namespace Saxl.FlagColumns
open Columns

lemma blocks_append (rs ss : List ℕ) {d : ℕ} (N : ℕ → Fin d → ℂ) :
    blocks (rs ++ ss) N = positionProduct (appendPositions rs ss) (blocks rs N) (blocks ss N) := by
  induction rs with
  | nil =>
    rw [blocks_nil]
    funext w
    change blocks ss N w = 1 * blocks ss N (rightWord (appendPositions [] ss) w)
    rw [one_mul]
    congr 1
    funext i
    apply congrArg w
    apply Fin.ext
    change i.val = 0 + i.val
    omega
  | cons r rs ih =>
    change blocks (r :: (rs ++ ss)) N = _
    rw [blocks_cons,blocks_cons,ih]
    funext w
    have hll : leftWord finSumFinEquiv.symm w =
        leftWord finSumFinEquiv.symm (leftWord (appendPositions (r::rs) ss) w) := by
      funext i
      apply congrArg w
      apply Fin.ext
      rfl
    have hlr : leftWord (appendPositions rs ss) (rightWord finSumFinEquiv.symm w) =
        rightWord finSumFinEquiv.symm (leftWord (appendPositions (r::rs) ss) w) := by
      funext i
      apply congrArg w
      apply Fin.ext
      rfl
    have hrr : rightWord (appendPositions rs ss) (rightWord finSumFinEquiv.symm w) =
        rightWord (appendPositions (r::rs) ss) w := by
      funext i
      apply congrArg w
      apply Fin.ext
      change r + (rs.sum+i.val) = (r+rs.sum)+i.val
      omega
    change wedge r N _ * (blocks rs N _ * blocks ss N _) =
      (wedge r N _ * blocks rs N _) * blocks ss N _
    rw [hll,hlr,hrr,mul_assoc]
    rfl

lemma standard_placed {rs : List ℕ} {μ : YoungDiagram} {D : ℕ}
    (e : Cells rs ≃ μ.cells)
    (hr : ∀ c, (e c).val.1 = row c)
    (hc : ∀ c c', (e c).val.2 = (e c').val.2 ↔ col c = col c')
    (hD : μ.colLen 0 ≤ D) :
    blocks rs (standard D) = letterLift (Fin.castLE hD) (polytabloid ((enumerate rs).trans e)) := by
  rw [← mapped_placed e hr hc (standard D)]
  unfold letterLift
  congr 2
  funext i a
  unfold standard
  simp only [Fin.ext_iff, Fin.val_castLE]

lemma letterLift_id_apply {n d : ℕ} (x : WordSpace n d) :
    letterLift (id : Fin d → Fin d) x = x := by
  classical
  have hx : x = ∑ w, x w • Pi.single w (1 : ℂ) := by
    funext w
    simp [Pi.single_apply]
  conv_lhs => rw [hx]
  rw [map_sum]
  simp only [map_smul, letterLift_single, Function.id_comp]
  exact hx.symm

lemma standard_placed_self {rs : List ℕ} {μ : YoungDiagram}
    (e : Cells rs ≃ μ.cells)
    (hr : ∀ c, (e c).val.1 = row c)
    (hc : ∀ c c', (e c).val.2 = (e c').val.2 ↔ col c = col c') :
    blocks rs (standard (μ.colLen 0)) = polytabloid ((enumerate rs).trans e) := by
  rw [standard_placed e hr hc le_rfl]
  exact letterLift_id_apply _

lemma standard_exists_tableau (rs : List ℕ) :
    ∃ t : Tableau rs.sum (columnShape rs),
      blocks rs (standard ((columnShape rs).colLen 0)) = polytabloid t := by
  obtain ⟨e,hr,hc⟩ := columnShape_placement rs
  exact ⟨(enumerate rs).trans e,standard_placed_self e hr hc⟩

end Saxl.FlagColumns
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_CoordinateLine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate Line. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

def coordinateRestriction {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (a : Fin n → Fin (μ.colLen 0)) : Module.Dual ℂ (Specht t) :=
  { toFun := fun x => x.val a
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_PairForms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pair Forms. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

def pairFormTensor {n m d : ℕ} (e : Fin n ≃ Fin m ⊕ Fin m)
    (B : Matrix (Fin d) (Fin d) ℂ) : WordSpace n d :=
  fun w => ∏ i, B (leftWord e w i) (rightWord e w i)

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_SingletonForms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Singleton Forms. -/

section

noncomputable section
namespace Saxl

def singleWord {d : ℕ} (v : Fin d → ℂ) : WordSpace 1 d := fun w => v (w 0)

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_ShortColumns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Short Columns. -/

section

noncomputable section
open scoped TensorProduct

namespace Saxl.ShortColumns

def oddTableau (b : ℕ) : Tableau (2*b+1) (shape b 1) where
  toFun i := if hi : i.val = 0 then ⟨(0,b), (mem_shape b 1 0 b).mpr (Or.inl ⟨rfl, by omega⟩)⟩
    else ⟨((i.val+1)%2,(i.val-1)/2), (mem_shape _ _ _ _).mpr (by
      have ht := i.isLt
      rcases Nat.mod_two_eq_zero_or_one (i.val+1) with h | h
      · exact Or.inl ⟨h, by omega⟩
      · exact Or.inr ⟨h, by omega⟩)⟩
  invFun c := if h : c.val.2 = b then ⟨0,by omega⟩ else
    ⟨2*c.val.2+c.val.1+1, by
      have hc := (mem_shape b 1 c.val.1 c.val.2).mp c.property
      change 2*c.val.2+c.val.1+1 < 2*b+1
      change c.val.2 ≠ b at h
      omega⟩
  left_inv i := by
    dsimp only
    by_cases hi : i.val = 0
    · simp only [dite_eq_left hi, dite_true]
      apply Fin.ext
      exact hi.symm
    · simp only [dite_eq_right hi]
      have hj : (i.val-1)/2 ≠ b := by have ht := i.isLt; omega
      simp only [dite_eq_right hj]
      apply Fin.ext
      dsimp only
      omega
  right_inv c := by
    have hc := (mem_shape b 1 c.val.1 c.val.2).mp c.property
    dsimp only
    by_cases h : c.val.2 = b
    · simp only [dite_eq_left h, dite_true]
      apply Subtype.ext
      apply Prod.ext <;> dsimp only <;> omega
    · simp only [dite_eq_right h]
      have h' : 2*c.val.2+c.val.1+1 ≠ 0 := by omega
      simp only [dite_eq_right h']
      apply Subtype.ext
      apply Prod.ext <;> dsimp only <;> omega

def evenTableau (b : ℕ) : Tableau (2*b) (shape b 0) where
  toFun i := ⟨(i.val%2,i.val/2), (mem_shape b 0 _ _).mpr (by
    have ht := i.isLt
    rcases Nat.mod_two_eq_zero_or_one i.val with h | h
    · exact Or.inl ⟨h,by omega⟩
    · exact Or.inr ⟨h,by omega⟩)⟩
  invFun c := ⟨2*c.val.2+c.val.1, by
    have hc := (mem_shape b 0 c.val.1 c.val.2).mp c.property
    omega⟩
  left_inv i := by apply Fin.ext; dsimp only; omega
  right_inv c := by
    have hc := (mem_shape b 0 c.val.1 c.val.2).mp c.property
    apply Subtype.ext
    apply Prod.ext <;> dsimp only <;> omega

def evenAlt (b : ℕ) : WordSpace (2*b) 2 :=
  altWord (fiberGroup (fun i : Fin (2*b) => i.val/2))
    (fun i => ⟨i.val%2,Nat.mod_lt _ (by omega)⟩)

end Saxl.ShortColumns
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_AttachmentTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Attachment Transfer. -/

section

noncomputable section
open scoped TensorProduct

namespace Saxl

def columnAmbientSignMap {n : ℕ} {α : YoungDiagram} (t : Tableau n α)
    (φ : (spechtRep t).Equiv (signTwist (spechtRep (transposeTableau t)))) :
    Representation.IntertwiningMap (wordRep n (α.colLen 0))
      (signTwist (wordRep n (α.transpose.colLen 0))) :=
  (signTwistMap (spechtInclusion (transposeTableau t))).comp
    (φ.toIntertwiningMap.comp (subrepProject (spechtSub t)
      (fun _ hx => cyclic_star _ (polytabloid_real _) hx)))

def columnPairAntiMap {n : ℕ} {α : YoungDiagram} (t : Tableau n α)
    (φ : (spechtRep t).Equiv (signTwist (spechtRep (transposeTableau t)))) :
    Representation.IntertwiningMap
      (signTwist (wordRep n (α.transpose.colLen 0 * α.colLen 0)))
      (wordRep n (α.transpose.colLen 0 * α.transpose.colLen 0)) :=
  (wordTensorEquiv _ _ _).toIntertwiningMap.comp
    ((tensorAnti (wordRep _ _) (columnAmbientSignMap t φ)).comp
      (signTwistMap (wordTensorEquiv _ _ _).symm.toIntertwiningMap))

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Band_OneExtra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One Extra. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

def columnSquareWord {n : ℕ} {α : YoungDiagram} (t : Tableau n α) :
    WordSpace n (α.colLen 0 * α.colLen 0) :=
  wordTensor _ _ _ (polytabloid t ⊗ₜ[ℂ] polytabloid t)

def columnSquareCyclic {n : ℕ} {α : YoungDiagram} (t : Tableau n α) :=
  cyclic (wordRep n (α.colLen 0 * α.colLen 0)) (columnSquareWord t)

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_DualTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dual Transfer. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

def tensorSignCancel {n : ℕ} {X Y : Type*} [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    (σ : Representation ℂ (Equiv.Perm (Fin n)) Y) :
    ((signTwist ρ).tprod (signTwist σ)).Equiv (ρ.tprod σ) where
  toLinearEquiv := LinearEquiv.refl ℂ _
  isIntertwining' g := by
    ext x y
    change (signC g • ρ g x) ⊗ₜ[ℂ] (signC g • σ g y) = ρ g x ⊗ₜ[ℂ] σ g y
    rw [TensorProduct.smul_tmul_smul, signC_mul_self, one_smul]

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_ProjectedTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Projected Tensor. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

def invariantCoordinateProjection {n d : ℕ}
    (P : (Fin n → Fin d) → Prop)
    (hP : ∀ (g : Equiv.Perm (Fin n)) w, P (w ∘ g) ↔ P w) :
    Representation.IntertwiningMap (wordRep n d) (wordRep n d) where
  toLinearMap := coordinateProjection P
  isIntertwining' g := by
    classical
    apply LinearMap.ext
    intro x
    funext w
    change (if P w then x (w ∘ g) else 0) = (if P (w ∘ g) then x (w ∘ g) else 0)
    rw [hP]

def projectedSpechtTensor {n : ℕ} {α β : YoungDiagram}
    (a : Tableau n α) (b : Tableau n β)
    (P : (Fin n → Fin (α.colLen 0 * β.colLen 0)) → Prop)
    (hP : ∀ (g : Equiv.Perm (Fin n)) w, P (w ∘ g) ↔ P w) :=
  ((invariantCoordinateProjection P hP).comp (spechtTensorMap a b)).range

def projectedTensorQuotient {n : ℕ} {α β : YoungDiagram}
    (a : Tableau n α) (b : Tableau n β)
    (P : (Fin n → Fin (α.colLen 0 * β.colLen 0)) → Prop)
    (hP : ∀ (g : Equiv.Perm (Fin n)) w, P (w ∘ g) ↔ P w) :
    Representation.IntertwiningMap ((spechtRep a).tprod (spechtRep b))
      (projectedSpechtTensor a b P hP).toRepresentation where
  toLinearMap := ((invariantCoordinateProjection P hP).comp
    (spechtTensorMap a b)).toLinearMap.rangeRestrict
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact LinearMap.congr_fun
      (((invariantCoordinateProjection P hP).comp (spechtTensorMap a b)).isIntertwining' g) x

def dualSignMap {n : ℕ} {α : YoungDiagram} (a : Tableau n α)
    (φ : (spechtRep a).Equiv (signTwist (spechtRep (transposeTableau a)))) :
    Representation.IntertwiningMap (spechtRep a).dual
      (signTwist (spechtRep (transposeTableau a))) :=
  φ.toIntertwiningMap.comp (spechtSelfDual a).symm.toIntertwiningMap

def dualTensorSignMap {n : ℕ} {α β : YoungDiagram}
    (a : Tableau n α) (b : Tableau n β)
    (φ : (spechtRep a).Equiv (signTwist (spechtRep (transposeTableau a))))
    (ψ : (spechtRep b).Equiv (signTwist (spechtRep (transposeTableau b)))) :
    Representation.IntertwiningMap ((spechtRep a).tprod (spechtRep b)).dual
      (wordRep n (α.transpose.colLen 0 * β.transpose.colLen 0)) :=
  (spechtTensorMap (transposeTableau a) (transposeTableau b)).comp
    ((tensorSignCancel (spechtRep (transposeTableau a))
      (spechtRep (transposeTableau b))).toIntertwiningMap.comp
      (((dualSignMap a φ).tensor (dualSignMap b ψ)).comp
        (tensorDualEquiv (spechtRep a) (spechtRep b)).symm.toIntertwiningMap))

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_Neighboring
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Neighboring. -/

section

noncomputable section
open scoped TensorProduct

namespace Saxl
namespace Balance

def inOutputs {n d e : ℕ} (I : Set ℕ) (w : Fin n → Fin (d*e)) : Prop :=
  ∀ i, output (w i) ∈ I

lemma inOutputs_invariant {n d e : ℕ} (I : Set ℕ)
    (g : Equiv.Perm (Fin n)) (w : Fin n → Fin (d*e)) :
    inOutputs I (w ∘ g) ↔ inOutputs I w := by
  constructor
  · intro h i
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using h (g.symm i)
  · intro h i
    exact h (g i)

def neighborLayer (r : ℕ) : Tableau (2*r+1) (ShortColumns.shape r 1) :=
  (ShortColumns.oddTableau r).trans (reverseShortColumns r)

def neighborTableau (r : ℕ) : Tableau (2*r+1) (ShortColumns.shape r 1).transpose :=
  transposeTableau (neighborLayer r)

def neighborRight (r : ℕ) : Tableau (2*r+1) (ShortColumns.shape r 1).transpose :=
  Fin.revPerm.trans (neighborTableau r)

end Balance
end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Balance_BalanceColumns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Balance Columns. -/

section

noncomputable section
open scoped TensorProduct

namespace Saxl.Balance

lemma component_sum_perm {n : ℕ} (c : Fin n → ℕ) (g : Equiv.Perm (Fin n))
    (hg : g ∈ fiberGroup c) (z : Fin n → ℤ) (k : ℕ) :
    ∑ i ∈ Finset.univ.filter (fun i => c i = k), z (g i) =
      ∑ i ∈ Finset.univ.filter (fun i => c i = k), z i := by
  classical
  have hh : ∀ i, c (g i) = c i := hg
  simpa only [hh] using perm_filter_sum g (fun i => c i = k) z

lemma fixedSumSpace_invariant {n d : ℕ} (c : Fin n → ℕ) (z : Fin d → ℤ)
    (σ : ℕ → ℤ) (g : Equiv.Perm (Fin n)) (hg : g ∈ fiberGroup c)
    (x : WordSpace n d) (hx : x ∈ fixedSumSpace c z σ) :
    wordRep n d g x ∈ fixedSumSpace c z σ := by
  intro w hw k
  have hh := hx (w ∘ g) hw k
  simpa only [Function.comp_apply, component_sum_perm c g hg (fun i => z (w i)) k] using hh

def columnRowSums {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (c : Fin n → ℕ) (k : ℕ) : ℤ :=
  ∑ i ∈ Finset.univ.filter (fun i => c i = k), (rowWord t i).val

lemma polytabloid_fixed_column_sums {n : ℕ} {μ : YoungDiagram}
    (t : Tableau n μ) (c : Fin n → ℕ)
    (hc : ∀ i j, (t i).val.2 = (t j).val.2 → c i = c j) :
    polytabloid t ∈ fixedSumSpace c (fun a : Fin (μ.colLen 0) => a.val)
      (columnRowSums t c) := by
  classical
  have hbase : (Pi.single (rowWord t) (1 : ℂ)) ∈
      fixedSumSpace c (fun a : Fin (μ.colLen 0) => a.val) (columnRowSums t c) := by
    intro w hw k
    have he : w = rowWord t := by
      by_contra hn
      exact hw (Pi.single_eq_of_ne hn _)
    subst w
    rfl
  unfold polytabloid
  apply Submodule.sum_mem
  intro g hg
  apply Submodule.smul_mem
  apply fixedSumSpace_invariant _ _ _ _ ?_ _ hbase
  intro i
  exact hc _ _ (g.property i)

def columnOutputSums {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (c : Fin n → ℕ) (k : ℕ) : ℤ :=
  2 * columnRowSums t c k + (Finset.univ.filter (fun i => c i = k)).card

end Saxl.Balance
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Balance_PackingSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Packing Support. -/

section

noncomputable section
open scoped TensorProduct MonoidAlgebra
namespace Saxl

theorem cyclic_supportLE_coind {G H X Y : Type*}
    [Group G] [Finite G] [Group H] [Finite H]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (ρ : Representation ℂ G X) (σ : Representation ℂ H Y)
    (φ : H →* G) (v : X)
    (T : Representation.IntertwiningMap σ (ρ.comp φ)) (hv : v ∈ T.range) :
    SupportLE (cyclic ρ v).toRepresentation (Representation.coind φ σ) := by
  apply intertwining_separates_of_simple_support
  intro S hS
  let := hS
  have hi : subrepInclusion S ≠ 0 := by
    intro hz
    let : Nontrivial S.toRepresentation.asModule :=
      IsSimpleModule.nontrivial ℂ[G] S.toRepresentation.asModule
    let : Nontrivial S.toSubmodule := S.toRepresentation.asModuleEquiv.symm.toEquiv.nontrivial
    obtain ⟨x,hx⟩ := exists_ne (0 : S.toSubmodule)
    apply hx
    apply Subtype.ext
    exact congrArg (fun f : Representation.IntertwiningMap S.toRepresentation
      (cyclic ρ v).toRepresentation => f x) hz
  obtain ⟨F,hF⟩ := cyclic_restriction_support S.toRepresentation σ ρ φ v T hv
    (subrepInclusion S) hi
  exact ⟨coindLift φ F,coindLift_ne_zero φ F hF⟩

theorem SupportLE.cyclic_image {G X Y Z : Type*} [Group G] [Finite G]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup Z] [Module ℂ Z]
    {ρ : Representation ℂ G X} {σ : Representation ℂ G Y}
    {τ : Representation ℂ G Z} (v : X)
    (T : Representation.IntertwiningMap ρ σ) (h : SupportLE (cyclic ρ v).toRepresentation τ) :
    SupportLE (cyclic σ (T v)).toRepresentation τ := by
  let Q := T.comp (subrepInclusion (cyclic ρ v))
  have hm : T v ∈ Q.range := ⟨⟨v,mem_cyclic ρ v⟩,rfl⟩
  obtain ⟨i,hi⟩ := subrepresentation_embeds_of_le_range Q (cyclic σ (T v))
    ((cyclic_le _ _ _).mpr hm)
  exact (SupportLE.of_injective i hi).trans h

theorem product_supportLE_coind {n a b d : ℕ} {G H X Y : Type*}
    [Group G] [Finite G] [Group H] [Finite H]
    [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X]
    [AddCommGroup Y] [Module ℂ Y] [FiniteDimensional ℂ Y]
    (φ : G →* Equiv.Perm (Fin a)) (ψ : H →* Equiv.Perm (Fin b))
    (ρ : Representation ℂ G X) (σ : Representation ℂ H Y)
    (e : Fin n ≃ Fin a ⊕ Fin b) (v : WordSpace a d) (u : WordSpace b d)
    (hv : SupportLE (cyclic (wordRep a d) v).toRepresentation (Representation.coind φ ρ))
    (hu : SupportLE (cyclic (wordRep b d) u).toRepresentation (Representation.coind ψ σ)) :
    SupportLE (cyclic (wordRep n d) (positionProduct e v u)).toRepresentation
      (Representation.coind ((sumPermHom e).comp (φ.prodMap ψ)) (outer ρ σ)) := by
  classical
  let : AddCommGroup ((cyclic (wordRep a d) v).toSubmodule ⊗[ℂ]
      (cyclic (wordRep b d) u).toSubmodule) := Module.addCommMonoidToAddCommGroup ℂ
  have h₀ := cyclic_supportLE_coind (wordRep n d)
    (outer (cyclic (wordRep a d) v).toRepresentation (cyclic (wordRep b d) u).toRepresentation)
    (sumPermHom e) (positionProduct e v u) (cyclicProductMap e v u) (cyclicProduct_mem_range e v u)
  have h₁ := (hv.outer hu).coind (sumPermHom e)
  have h₂ := (SupportLE.of_injective (coindOuter φ ψ ρ σ)
    (coindOuter_injective φ ψ ρ σ)).coind (sumPermHom e)
  have h₃ := SupportLE.of_injective (coindTrans (φ.prodMap ψ) (sumPermHom e) (outer ρ σ))
    (coindTrans_injective (φ.prodMap ψ) (sumPermHom e) (outer ρ σ))
  exact ((h₀.trans h₁).trans h₂).trans h₃

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_WordRelabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Word Relabel. -/

section

noncomputable section
namespace Saxl
open scoped TensorProduct

lemma letterLift_wordTensor {n a b c d : ℕ} (f : Fin a → Fin c) (g : Fin b → Fin d)
    (x : WordSpace n a) (y : WordSpace n b) :
    letterLift (pairLetterMap f g) (wordTensor n a b (x ⊗ₜ[ℂ] y)) =
      wordTensor n c d (letterLift f x ⊗ₜ[ℂ] letterLift g y) := by
  classical
  conv_lhs => rw [← (Pi.basisFun ℂ (Fin n → Fin a)).sum_repr x,
    ← (Pi.basisFun ℂ (Fin n → Fin b)).sum_repr y]
  conv_rhs => rw [← (Pi.basisFun ℂ (Fin n → Fin a)).sum_repr x,
    ← (Pi.basisFun ℂ (Fin n → Fin b)).sum_repr y]
  simp only [TensorProduct.sum_tmul, TensorProduct.tmul_sum, map_sum, map_smul,
    TensorProduct.smul_tmul, TensorProduct.tmul_smul, Pi.basisFun_apply,
    wordTensor_single, letterLift_single]
  have hm (p : Fin n → Fin a) (q : Fin n → Fin b) :
      pairLetterMap f g ∘ mergeWords p q = mergeWords (f ∘ p) (g ∘ q) := by
    funext i
    simp only [Function.comp_apply, pairLetterMap, mergeWords, Equiv.symm_apply_apply]
  simp only [hm]

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Balance_BalanceGluing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Balance Gluing. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl.Balance

lemma cyclicSquareMap_polytabloid {n : ℕ} {lam : YoungDiagram} (a : Tableau n lam) :
    cyclicSquareMap (polytabloid a) = spechtTensorMap a a := by
  unfold spechtTensorMap
  rfl

end Saxl.Balance
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Balance_BalanceLeaves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Balance Leaves. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl.Balance

def singleFiberHom (n k : ℕ) : Equiv.Perm (Fin n) →* fiberGroup (fun _ : Fin n => k) where
  toFun g := ⟨g,fun _ => rfl⟩
  map_one' := rfl
  map_mul' _ _ := rfl

lemma singleFiberHom_surjective (n k : ℕ) : Function.Surjective (singleFiberHom n k) :=
  fun g => ⟨g.val,Subtype.ext rfl⟩

lemma specht_fixed_single_sum {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (k : ℕ) (x : Specht t) :
    x.val ∈ fixedSumSpace (fun _ : Fin n => k) (fun a : Fin (μ.colLen 0) => a.val)
      (columnRowSums t (fun _ => k)) := by
  rcases x with ⟨x,hx⟩
  change x ∈ Submodule.span ℂ (Set.range fun g : Equiv.Perm (Fin n) =>
    wordRep n (μ.colLen 0) g (polytabloid t)) at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨g,rfl⟩ := hy
    exact fixedSumSpace_invariant _ _ _ g (fun _ => rfl) _
      (polytabloid_fixed_column_sums t _ (fun _ _ _ => rfl))
  | zero => exact Submodule.zero_mem _
  | add x y hx hy ihx ihy => exact Submodule.add_mem _ ihx ihy
  | smul a x hx ih => exact Submodule.smul_mem _ a ih

lemma spechtTensor_fixed_single_sum {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (k : ℕ) (x : Specht t ⊗[ℂ] Specht t) :
    FixedComponentSums (fun _ : Fin n => k) (fun a => (output a : ℤ))
      (columnOutputSums t (fun _ => k)) (spechtTensorMap t t x) := by
  classical
  change spechtTensorMap t t x ∈ fixedSumSpace (fun _ : Fin n => k)
    (fun a => (output a : ℤ)) (columnOutputSums t (fun _ => k))
  induction x using OAI.tensorInductionOn with
  | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  | tmul x y =>
    intro w hw i
    rw [spechtTensorMap] at hw
    change wordTensor _ _ _ (x.val ⊗ₜ[ℂ] y.val) w ≠ 0 at hw
    rw [wordTensor_tmul] at hw
    obtain ⟨hx,hy⟩ := mul_ne_zero_iff.mp hw
    have hs₁ := specht_fixed_single_sum t k x (splitLeft w) hx i
    have hs₂ := specht_fixed_single_sum t k y (splitRight w) hy i
    change (∑ p ∈ Finset.univ.filter (fun _ : Fin n => k = i), (output (w p) : ℤ)) = _
    simp only [output, Nat.cast_add, Nat.cast_one, Finset.sum_add_distrib,
      Finset.sum_const, nsmul_eq_mul, mul_one]
    change (∑ p ∈ Finset.univ.filter (fun _ : Fin n => k = i), ((splitLeft w p).val : ℤ)) +
      (∑ p ∈ Finset.univ.filter (fun _ : Fin n => k = i), ((splitRight w p).val : ℤ)) + _ = _
    rw [hs₁,hs₂]
    dsimp only [columnOutputSums]
    ring

lemma componentWords_single {n d : ℕ} (k : ℕ) (I : Set ℕ)
    (A : Fin (d*d) → Prop) (label : Fin (d*d) → ℕ)
    (h : ∀ a, (A a ∧ label a = k) ↔ output a ∈ I) (w : Fin n → Fin (d*d)) :
    componentWords (fun _ : Fin n => k) A label w ↔ inOutputs I w := by
  constructor
  · rintro ⟨hA,hl⟩ i
    exact (h _).mp ⟨hA i,hl i⟩
  · intro hw
    exact ⟨fun i => ((h _).mpr (hw i)).1,fun i => ((h _).mpr (hw i)).2⟩

def projectedPiece {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (k : ℕ) (I : Set ℕ)
    (A : Fin (μ.colLen 0 * μ.colLen 0) → Prop)
    (label : Fin (μ.colLen 0 * μ.colLen 0) → ℕ)
    (h : ∀ a, (A a ∧ label a = k) ↔ output a ∈ I) :
    Piece (polytabloid t) (fun _ : Fin n => k) A label
      (columnOutputSums t (fun _ => k)) (singleFiberHom n k)
      (projectedSpechtTensor t t (inOutputs I) (inOutputs_invariant I)).toRepresentation := by
  let W := projectedSpechtTensor t t (inOutputs I) (inOutputs_invariant I)
  let Q := projectedTensorQuotient t t (inOutputs I) (inOutputs_invariant I)
  have hQ : Function.Surjective Q := by
    rintro ⟨y,x,rfl⟩
    exact ⟨x,rfl⟩
  letI : AddCommGroup (Specht t ⊗[ℂ] Specht t) := Module.addCommMonoidToAddCommGroup ℂ
  let s := Classical.choose (intertwining_lift_surjective Q hQ
    (Representation.IntertwiningMap.id W.toRepresentation))
  have hs := Classical.choose_spec (intertwining_lift_surjective Q hQ
    (Representation.IntertwiningMap.id W.toRepresentation))
  let T : Representation.IntertwiningMap W.toRepresentation
      ((wordRep n (μ.colLen 0 * μ.colLen 0)).comp
        ((fiberGroup (fun _ : Fin n => k)).subtype.comp (singleFiberHom n k))) :=
    subrepInclusion W
  refine {
    surj := singleFiberHom_surjective n k
    raw := (spechtTensorMap t t).toLinearMap.comp s.toLinearMap
    raw_mem := ?_
    raw_sums := fun y => spechtTensor_fixed_single_sum t k (s y)
    projected := T
    injective := Subtype.val_injective
    projection_eq := ?_ }
  · intro y
    refine ⟨s y,?_⟩
    change cyclicSquareMap (polytabloid t) (s y) = spechtTensorMap t t (s y)
    rw [cyclicSquareMap_polytabloid]
    rfl
  · intro y
    have he := congrArg Subtype.val (congrArg (fun F : Representation.IntertwiningMap
      W.toRepresentation W.toRepresentation => F y) hs)
    change coordinateProjection (inOutputs I) (spechtTensorMap t t (s y)) = y.val at he
    change coordinateProjection (componentWords (fun _ : Fin n => k) A label)
      (spechtTensorMap t t (s y)) = y.val
    convert he using 2
    all_goals try with_reducible_and_instances rfl
    apply congrArg coordinateProjection
    funext w
    exact propext (componentWords_single k I A label h w)

end Saxl.Balance
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Balance_BalanceLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Balance Lift. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

lemma coordinateProjection_letterLift {n d D : ℕ} (f : Fin d → Fin D)
    (P : (Fin n → Fin d) → Prop) (Q : (Fin n → Fin D) → Prop)
    (h : ∀ w, Q (f ∘ w) ↔ P w) (x : WordSpace n d) :
    coordinateProjection Q (letterLift f x) = letterLift f (coordinateProjection P x) := by
  classical
  conv_lhs => rw [← (Pi.basisFun ℂ (Fin n → Fin d)).sum_repr x]
  conv_rhs => rw [← (Pi.basisFun ℂ (Fin n → Fin d)).sum_repr x]
  simp only [map_sum,map_smul,Pi.basisFun_apply,letterLift_single,
    coordinateProjection_single,h]
  apply Finset.sum_congr rfl
  intro w hw
  by_cases hp : P w <;> simp [hp,letterLift_single]

lemma letterLift_nonzero_word {n d D : ℕ} (f : Fin d → Fin D) (hf : Function.Injective f)
    (x : WordSpace n d) (w : Fin n → Fin D) (hw : letterLift f x w ≠ 0) :
    ∃ a : Fin n → Fin d, f ∘ a = w ∧ x a ≠ 0 := by
  classical
  have hm := letterLift_mem_alphabet (Set.range f) f (fun a => ⟨a,rfl⟩) x
  have hr : ∀ i, ∃ a, f a = w i := by
    intro i
    by_contra hi
    exact hw (hm w ⟨i,hi⟩)
  choose a ha using hr
  have he : f ∘ a = w := funext ha
  refine ⟨a,he,?_⟩
  rw [←he,letterLift_eval f hf] at hw
  exact hw

namespace Balance

lemma output_pairLetterMap {d D : ℕ} (f : Fin d → Fin D)
    (hf : ∀ a, (f a).val = a.val) (a : Fin (d*d)) :
    output (pairLetterMap f f a) = output a := by
  simp only [output,pairLetterMap,Equiv.symm_apply_apply,hf]

lemma cyclicSquareMap_lift_mem {n d D : ℕ} (f : Fin d → Fin D)
    (v : WordSpace n d) (x : WordSpace n (d*d))
    (hx : x ∈ (cyclicSquareMap v).range) :
    letterLift (pairLetterMap f f) x ∈ (cyclicSquareMap (letterLift f v)).range := by
  obtain ⟨z,rfl⟩ := hx
  let F := cyclicMap (letterLift f) v
  refine ⟨TensorProduct.map F.toLinearMap F.toLinearMap z,?_⟩
  induction z using OAI.tensorInductionOn with
  | add x y hx hy => simp only [map_add,hx,hy]
  | tmul x y =>
    change wordTensor _ _ _ (letterLift f x.val ⊗ₜ[ℂ] letterLift f y.val) =
      letterLift (pairLetterMap f f) (wordTensor _ _ _ (x.val ⊗ₜ[ℂ] y.val))
    exact (letterLift_wordTensor f f x.val y.val).symm

def Piece.lift {n d D : ℕ} {G Y : Type*} [Group G] [AddCommGroup Y] [Module ℂ Y]
    {v : WordSpace n d} {c : Fin n → ℕ} {σ : ℕ → ℤ}
    {φ : G →* fiberGroup c} {τ : Representation ℂ G Y}
    (f : Fin d → Fin D) (hf : ∀ a, (f a).val = a.val)
    (A : Fin (D*D) → Prop) (label : Fin (D*D) → ℕ)
    (P : Piece v c (A ∘ pairLetterMap f f) (label ∘ pairLetterMap f f) σ φ τ) :
    Piece (letterLift f v) c A label σ φ τ := by
  have hfi : Function.Injective f := by
    intro a b he
    apply Fin.ext
    simpa only [hf] using congrArg Fin.val he
  let J := pairLetterMap f f
  have hJi : Function.Injective J := pairLetterMap_injective f f hfi hfi
  let T : Representation.IntertwiningMap
      ((wordRep n (d*d)).comp ((fiberGroup c).subtype.comp φ))
      ((wordRep n (D*D)).comp ((fiberGroup c).subtype.comp φ)) :=
    ⟨(letterLift J).toLinearMap, fun g => (letterLift J).isIntertwining' (φ g).val⟩
  refine {
    surj := P.surj
    raw := (letterLift J).toLinearMap.comp P.raw
    raw_mem := fun y => cyclicSquareMap_lift_mem f v _ (P.raw_mem y)
    raw_sums := ?_
    projected := T.comp P.projected
    injective := (letterLift_injective J hJi).comp P.injective
    projection_eq := ?_ }
  · intro y w hw k
    obtain ⟨a,rfl,ha⟩ := letterLift_nonzero_word J hJi (P.raw y) w hw
    have he := P.raw_sums y a ha k
    simpa only [J, Function.comp_apply,output_pairLetterMap f hf] using he
  · intro y
    change coordinateProjection (componentWords c A label) (letterLift J (P.raw y)) =
      letterLift J (P.projected y)
    rw [coordinateProjection_letterLift J (componentWords c (A ∘ J) (label ∘ J))
      (componentWords c A label) (fun _ => Iff.rfl),P.projection_eq]

end Balance
end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Balance_BalancePacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Balance Packing. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl.Balance

def Packing.join {n a b d E : ℕ} {v : WordSpace a d} {u : WordSpace b d}
    {A : Fin (d*d) → Prop} {label : Fin (d*d) → ℕ}
    {w : WordSpace a E} {z : WordSpace b E}
    (P : Packing v A label w) (Q : Packing u A label z)
    (e : Fin n ≃ Fin a ⊕ Fin b) (hd : ∀ i j, P.c i ≠ Q.c j) :
    Packing (positionProduct e v u) A label (positionProduct e w z) := by
  letI : AddCommGroup (P.Y ⊗[ℂ] Q.Y) := Module.addCommMonoidToAddCommGroup ℂ
  exact {
    G := P.G × Q.G
    Y := P.Y ⊗[ℂ] Q.Y
    c := joinedLabels e P.c Q.c
    σ := P.σ + Q.σ
    φ := (joinedFiberHom e P.c Q.c).comp (P.φ.prodMap Q.φ)
    τ := outer P.τ Q.τ
    piece := P.piece.join Q.piece e hd
    support := product_supportLE_coind
      ((fiberGroup P.c).subtype.comp P.φ) ((fiberGroup Q.c).subtype.comp Q.φ)
      P.τ Q.τ e w z P.support Q.support }

def Packing.map {n d e E : ℕ} {v : WordSpace n d}
    {A : Fin (d*d) → Prop} {label : Fin (d*d) → ℕ} {w : WordSpace n e}
    (P : Packing v A label w)
    (T : Representation.IntertwiningMap (wordRep n e) (wordRep n E)) :
    Packing v A label (T w) :=
  { P with support := P.support.cyclic_image w T }

def Packing.lift {n d D e : ℕ} {v : WordSpace n d} {w : WordSpace n e}
    (f : Fin d → Fin D) (hf : ∀ a, (f a).val = a.val)
    (A : Fin (D*D) → Prop) (label : Fin (D*D) → ℕ)
    (P : Packing v (A ∘ pairLetterMap f f) (label ∘ pairLetterMap f f) w) :
    Packing (letterLift f v) A label w :=
  { P with piece := P.piece.lift f hf A label }

def boundedPacking {n e : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (k : ℕ) (I : Set ℕ)
    (A : Fin (μ.colLen 0 * μ.colLen 0) → Prop)
    (label : Fin (μ.colLen 0 * μ.colLen 0) → ℕ)
    (h : ∀ a, (A a ∧ label a = k) ↔ output a ∈ I)
    (hs : SupportLE (wordRep n e)
      (projectedSpechtTensor t t (inOutputs I) (inOutputs_invariant I)).toRepresentation)
    (w : WordSpace n e) : Packing (polytabloid t) A label w := by
  let W := projectedSpechtTensor t t (inOutputs I) (inOutputs_invariant I)
  let φ := (fiberGroup (fun _ : Fin n => k)).subtype.comp (singleFiberHom n k)
  have hi : Function.Injective (coindLift (ρ := W.toRepresentation) φ (Representation.IntertwiningMap.id W.toRepresentation)) := by
    intro x y hxy
    have he := congrArg (fun z : Representation.coindV φ W.toRepresentation => z.val 1) hxy
    change W.toRepresentation 1 x = W.toRepresentation 1 y at he
    simpa only [map_one,Module.End.one_apply] using he
  refine {
    G := Equiv.Perm (Fin n)
    Y := W.toSubmodule
    c := fun _ => k
    σ := columnOutputSums t (fun _ => k)
    φ := singleFiberHom n k
    τ := W.toRepresentation
    piece := projectedPiece t k I A label h
    support := ?_ }
  exact ((SupportLE.of_injective (subrepInclusion (cyclic (wordRep n e) w))
    Subtype.val_injective).trans hs).trans (SupportLE.of_injective _ hi)

end Saxl.Balance
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_WordContents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Word Contents. -/

section

noncomputable section
namespace Saxl
open scoped BigOperators

lemma wordContent_position_join {n a b d e E : ℕ}
    (p : Fin n ≃ Fin a ⊕ Fin b) (q : Fin E ≃ Fin d ⊕ Fin e)
    (w : Fin a → Fin d) (z : Fin b → Fin e) (j : Fin E) :
    wordContent
      ((positionWordsEquiv p).symm ((fun i => q.symm (Sum.inl (w i))),
        (fun i => q.symm (Sum.inr (z i))))) j =
      Sum.elim (wordContent w) (wordContent z) (q j) := by
  classical
  rw [wordContent, Finset.card_filter]
  rw [← Equiv.sum_comp p.symm]
  rw [Fintype.sum_sum_type]
  rcases hj : q j with k | k
  · have hqq : j = q.symm (Sum.inl k) := (q.eq_symm_apply).mpr hj
    subst j
    simp only [positionWordsEquiv, Equiv.coe_fn_symm_mk, joinPositions, Equiv.apply_symm_apply, Sum.elim_inl,
      Sum.elim_inr, q.symm.injective.eq_iff,
      Sum.inl.injEq, Sum.inr_ne_inl, ite_false, if_false, Finset.sum_const_zero, add_zero]
    rw [wordContent,Finset.card_filter]
  · have hqq : j = q.symm (Sum.inr k) := (q.eq_symm_apply).mpr hj
    subst j
    simp only [positionWordsEquiv, Equiv.coe_fn_symm_mk, joinPositions, Equiv.apply_symm_apply, Sum.elim_inl,
      Sum.elim_inr, q.symm.injective.eq_iff,
      Sum.inr.injEq, Sum.inl_ne_inr, ite_false, if_false, Finset.sum_const_zero, zero_add]
    rw [wordContent,Finset.card_filter]

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Balance_WordPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Word Packing. -/

section

noncomputable section
namespace Saxl
open scoped BigOperators

lemma single_joinPositions {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (w : Fin a → Fin d) (z : Fin b → Fin d) :
    positionProduct e (Pi.single w 1) (Pi.single z 1) =
      Pi.single ((positionWordsEquiv e).symm (w,z)) 1 := by
  have hl := congrArg Prod.fst ((positionWordsEquiv e).apply_symm_apply (w,z))
  have hr := congrArg Prod.snd ((positionWordsEquiv e).apply_symm_apply (w,z))
  change leftWord e ((positionWordsEquiv e).symm (w,z)) = w at hl
  change rightWord e ((positionWordsEquiv e).symm (w,z)) = z at hr
  rw [single_positionProduct e,hl,hr]

namespace Balance
open FlagColumns Columns

structure WordPacking (rs ps : List ℕ) (d : ℕ)
    (A : Fin (d*d) → Prop) (label : Fin (d*d) → ℕ) (marks : Finset ℕ) where
  word : Fin rs.sum → Fin ps.length
  counts : ∀ j, wordContent word j = ps.get j
  packing : Packing (blocks rs (standard d)) A label (Pi.single word 1)
  marksBound : ∀ i, packing.c i ∈ marks

def WordPacking.join {rs ss ps qs : List ℕ} {d : ℕ}
    {A : Fin (d*d) → Prop} {label : Fin (d*d) → ℕ} {marks marks' : Finset ℕ}
    (P : WordPacking rs ps d A label marks) (Q : WordPacking ss qs d A label marks')
    (hdis : Disjoint marks marks') : WordPacking (rs++ss) (ps++qs) d A label (marks ∪ marks') := by
  classical
  let e := appendPositions rs ss
  let f := appendLetters ps qs
  let wi := f.symm ∘ Sum.inl ∘ P.word
  let zi := f.symm ∘ Sum.inr ∘ Q.word
  let P' := P.packing.map (letterLift (f.symm ∘ Sum.inl))
  let Q' := Q.packing.map (letterLift (f.symm ∘ Sum.inr))
  have hd : ∀ i j, P'.c i ≠ Q'.c j := by
    intro i j hij
    have h₁ := P.marksBound i
    have h₂ := Q.marksBound j
    change P.packing.c i = Q.packing.c j at hij
    rw [← hij] at h₂
    exact Finset.disjoint_left.mp hdis h₁ h₂
  let R := P'.join Q' e hd
  have hv : positionProduct e (blocks rs (standard d)) (blocks ss (standard d)) =
      blocks (rs++ss) (standard d) := (blocks_append rs ss _).symm
  have hw : positionProduct e (letterLift (f.symm ∘ Sum.inl) (Pi.single P.word 1))
      (letterLift (f.symm ∘ Sum.inr) (Pi.single Q.word 1)) =
      Pi.single ((positionWordsEquiv e).symm (wi,zi)) 1 := by
    rw [letterLift_single,letterLift_single,single_joinPositions]
    rfl
  refine {
    word := (positionWordsEquiv e).symm (wi,zi)
    counts := ?_
    packing := R.congr hv hw
    marksBound := ?_ }
  · intro j
    change wordContent ((positionWordsEquiv e).symm
      ((fun i => f.symm (Sum.inl (P.word i))), (fun i => f.symm (Sum.inr (Q.word i))))) j = _
    rw [wordContent_position_join e f P.word Q.word j, get_appendLetters]
    rcases h : f j with j | j
    · exact P.counts j
    · exact Q.counts j
  · intro i
    change joinedLabels e P.packing.c Q.packing.c i ∈ marks ∪ marks'
    unfold joinedLabels
    rcases e i with i | i
    · exact Finset.mem_union_left _ (P.marksBound i)
    · exact Finset.mem_union_right _ (Q.marksBound i)

def WordPacking.sorted {rs ps : List ℕ} {d : ℕ}
    {A : Fin (d*d) → Prop} {label : Fin (d*d) → ℕ} {marks : Finset ℕ}
    (P : WordPacking rs ps d A label marks) (hp : ∀ p ∈ ps, 0 < p) :
    WordPacking rs (columnShape ps).transpose.rowLens d A label marks := by
  classical
  let q := Classical.choose (list_get_equiv (columnShape_rows_permutation ps hp))
  have hq := Classical.choose_spec (list_get_equiv (columnShape_rows_permutation ps hp))
  refine {
    word := q ∘ P.word
    counts := ?_
    packing := (P.packing.map (letterLift q)).congr rfl (letterLift_single q P.word)
    marksBound := P.marksBound }
  intro j
  rw [wordContent_lift_equiv,P.counts,← hq,Equiv.apply_symm_apply]

end Balance
end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Balance_ConstantOutputs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Constant Outputs. -/

section

noncomputable section
open scoped TensorProduct Classical
namespace Saxl.Balance

def constantOutputMap (n d k : ℕ) :
    Representation.IntertwiningMap (wordRep n (d*d)) (wordRep n 1) :=
  wordMap (fun a _ => if output a = k then 1 else 0)

lemma constantOutputMap_single {n d : ℕ} (k : ℕ) (w : Fin n → Fin (d*d))
    (z : Fin n → Fin 1) :
    constantOutputMap n d k (Pi.single w 1) z =
      if inOutputs {k} w then 1 else 0 := by
  classical
  rw [constantOutputMap,wordMap_single]
  by_cases h : inOutputs {k} w
  · rw [ite_eq_left h]
    have he : ∀ i, output (w i) = k := h
    simp only [he,ite_true, if_true,Finset.prod_const_one]
  · rw [ite_eq_right h]
    change ¬ ∀ i, output (w i) = k at h
    push Not at h
    obtain ⟨i,hi⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

lemma constantOutputMap_projection {n d : ℕ} (k : ℕ) (x : WordSpace n (d*d)) :
    constantOutputMap n d k (coordinateProjection (inOutputs {k}) x) =
      constantOutputMap n d k x := by
  classical
  rw [← (Pi.basisFun ℂ (Fin n → Fin (d*d))).sum_repr x]
  simp only [map_sum,map_smul,Pi.basisFun_apply,coordinateProjection_single]
  apply Finset.sum_congr rfl
  intro w hw
  by_cases h : inOutputs {k} w
  · rw [ite_eq_left h]
  · rw [ite_eq_right h,map_zero,smul_zero]
    funext z
    simp only [Pi.zero_apply,Pi.smul_apply,smul_eq_mul,constantOutputMap_single,ite_eq_right h,mul_zero]

lemma constantOutputMap_pairSum {n d e : ℕ} (k : ℕ)
    (t : Fin n → Fin e) (ht : ∀ i, (t i).val+1 = k)
    (x : WordSpace n (d*d)) (z : Fin n → Fin 1) :
    constantOutputMap n d k x z = pairSumMap n d e x t := by
  classical
  rw [← (Pi.basisFun ℂ (Fin n → Fin (d*d))).sum_repr x]
  simp only [map_sum,map_smul,Pi.basisFun_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro w hw
  congr 1
  rw [constantOutputMap_single,← merge_split w,pairSumMap_single]
  congr 1
  apply propext
  change (∀ i, output (mergeWords (splitLeft w) (splitRight w) i) = k) ↔ _
  simp only [mergeWords,output,Equiv.symm_apply_apply]
  constructor <;> intro h i <;> have hi := ht i <;> have he := h i <;> omega

theorem constant_output_support {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (k : ℕ) (hk : ∀ i, (columnLengthWord t i).val+1 = k) :
    SupportLE (wordRep n 1)
      (projectedSpechtTensor t t (inOutputs {k}) (inOutputs_invariant {k})).toRepresentation := by
  classical
  let W := projectedSpechtTensor t t (inOutputs {k}) (inOutputs_invariant {k})
  let Q := (constantOutputMap n (μ.colLen 0) k).comp (subrepInclusion W)
  let v : Specht t := ⟨polytabloid t,mem_cyclic _ _⟩
  let y := projectedTensorQuotient t t (inOutputs {k}) (inOutputs_invariant {k}) (v ⊗ₜ[ℂ] v)
  let C : ℂ := (Nat.card (columnGroup t) : ℂ) * signC (columnReversal t).val
  have hC : C ≠ 0 := column_projection_coefficient_ne_zero t
  have hy (z : Fin n → Fin 1) : Q y z = C := by
    change constantOutputMap n (μ.colLen 0) k
      (coordinateProjection (inOutputs {k}) (spechtTensorMap t t (v ⊗ₜ[ℂ] v))) z = C
    rw [constantOutputMap_projection,constantOutputMap_pairSum k (columnLengthWord t) hk]
    have he := congrFun (squared_polytabloid_projection t) (columnLengthWord t)
    change (if wordOrbit (columnLengthWord t) (columnLengthWord t) then
      pairSumMap n (μ.colLen 0) (μ.colLen 0)
        (wordTensor _ _ _ (polytabloid t ⊗ₜ[ℂ] polytabloid t)) (columnLengthWord t) else 0) = _ at he
    rw [ite_eq_left ⟨1,rfl⟩,Pi.smul_apply,Pi.single_eq_same,smul_eq_mul,mul_one] at he
    unfold spechtTensorMap
    exact he
  have hQ : Function.Surjective Q := by
    intro x
    let z : Fin n → Fin 1 := fun _ => 0
    refine ⟨(x z / C) • y,?_⟩
    funext w
    rw [map_smul,Pi.smul_apply,smul_eq_mul,hy]
    have he : z = w := Subsingleton.elim _ _
    rw [div_mul_cancel₀ _ hC,he]
  obtain ⟨s,hs⟩ := intertwining_lift_surjective Q hQ
    (Representation.IntertwiningMap.id (wordRep n 1))
  apply SupportLE.of_injective s
  intro x y hxy
  have he := congrArg Q hxy
  change (Q.comp s) x = (Q.comp s) y at he
  rw [hs] at he
  exact he

end Saxl.Balance
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Balance_WordPackingLeaves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Word Packing Leaves. -/

section

noncomputable section
namespace Saxl.Balance
open FlagColumns Columns

def WordPacking.bounded {rs ps : List ℕ} {μ : YoungDiagram} {d E : ℕ}
    (e : Cells rs ≃ μ.cells)
    (hr : ∀ c, (e c).val.1 = row c)
    (hc : ∀ c c', (e c).val.2 = (e c').val.2 ↔ col c = col c')
    (hD : μ.colLen 0 ≤ d) (hps : ps.sum = rs.sum) (hone : ps.length ≤ E)
    (k : ℕ) (I : Set ℕ) (A : Fin (d*d) → Prop) (label : Fin (d*d) → ℕ)
    (he : ∀ a, (A a ∧ label a = k) ↔ output a ∈ I)
    (hs : SupportLE (wordRep rs.sum E)
      (projectedSpechtTensor ((enumerate rs).trans e) ((enumerate rs).trans e)
        (inOutputs I) (inOutputs_invariant I)).toRepresentation) :
    WordPacking rs ps d A label {k} := by
  classical
  let f := Fin.castLE hD
  let w := Classical.choose (exists_word_of_parts ps hps)
  have hw := Classical.choose_spec (exists_word_of_parts ps hps)
  have hlocal : ∀ a, ((A ∘ pairLetterMap f f) a ∧
      (label ∘ pairLetterMap f f) a = k) ↔ output a ∈ I := by
    intro a
    rw [Function.comp_apply,Function.comp_apply,he,output_pairLetterMap f (fun _ => rfl)]
  have hs' : SupportLE (wordRep rs.sum ps.length)
      (projectedSpechtTensor ((enumerate rs).trans e) ((enumerate rs).trans e)
        (inOutputs I) (inOutputs_invariant I)).toRepresentation :=
    (SupportLE.of_injective (letterLift (Fin.castLE hone))
      (letterLift_injective _ (Fin.castLE_injective hone))).trans hs
  let P := boundedPacking ((enumerate rs).trans e) k I
    (A ∘ pairLetterMap f f) (label ∘ pairLetterMap f f) hlocal hs' (Pi.single w 1)
  let Q := P.lift f (fun _ => rfl) A label
  refine {
    word := w
    counts := hw
    packing := Q.congr (standard_placed e hr hc hD).symm rfl
    marksBound := ?_ }
  intro i
  change k ∈ ({k} : Finset ℕ)
  simp

end Saxl.Balance
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Balance_EmptyPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Empty Packing. -/

section

noncomputable section
namespace Saxl.Balance
open FlagColumns Columns

def WordPacking.empty (d : ℕ) (A : Fin (d*d) → Prop) (label : Fin (d*d) → ℕ) :
    WordPacking [] [] d A label ∅ := by
  classical
  let e := Classical.choose (columnShape_placement [])
  have hr := (Classical.choose_spec (columnShape_placement [])).1
  have hc := (Classical.choose_spec (columnShape_placement [])).2
  let μ := columnShape []
  have h0 : μ.colLen 0 = 0 := by
    apply Nat.eq_zero_of_not_pos
    intro h
    have hmem : (0,0) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr h
    exact isEmptyElim (e.symm ⟨(0,0),hmem⟩)
  let t := (enumerate []).trans e
  let f := Fin.castLE (show μ.colLen 0 ≤ d by omega)
  have he : ∀ a, ((A ∘ pairLetterMap f f) a ∧
      (label ∘ pairLetterMap f f) a = 0) ↔ output a ∈ ({0}:Set ℕ) := by
    intro a
    have hh := a.isLt
    simp only [h0,Nat.zero_mul] at hh
    omega
  have hs : SupportLE (wordRep 0 0)
      (projectedSpechtTensor t t (inOutputs {0}) (inOutputs_invariant {0})).toRepresentation :=
    (SupportLE.of_injective (letterLift (Fin.castLE (show 0 ≤ 1 by omega)))
      (letterLift_injective _ (Fin.castLE_injective _))).trans
      (constant_output_support t 0 (fun i => Fin.elim0 i))
  let w : Fin 0 → Fin 0 := Fin.elim0
  let P := boundedPacking t 0 {0} (A ∘ pairLetterMap f f) (label ∘ pairLetterMap f f)
    he hs (Pi.single w 1)
  let Q := P.lift f (fun _ => rfl) A label
  exact {
    word := w
    counts := fun j => Fin.elim0 j
    packing := Q.congr (standard_placed e hr hc (show μ.colLen 0 ≤ d by omega)).symm rfl
    marksBound := fun i => Fin.elim0 i }

end Saxl.Balance
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Balance_WordPackingPairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Word Packing Pairs. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl.Balance
open FlagColumns Columns

def placedPiece {rs : List ℕ} {μ : YoungDiagram} {d : ℕ}
    (e : Cells rs ≃ μ.cells)
    (hr : ∀ c, (e c).val.1 = row c)
    (hc : ∀ c c', (e c).val.2 = (e c').val.2 ↔ col c = col c')
    (hd : μ.colLen 0 ≤ d) (k : ℕ) (I : Set ℕ)
    (A : Fin (d*d) → Prop) (label : Fin (d*d) → ℕ)
    (he : ∀ a, (A a ∧ label a = k) ↔ output a ∈ I) :
    Piece (blocks rs (standard d)) (fun _ => k) A label
      (columnOutputSums ((enumerate rs).trans e) (fun _ => k)) (singleFiberHom rs.sum k)
      (projectedSpechtTensor ((enumerate rs).trans e) ((enumerate rs).trans e)
        (inOutputs I) (inOutputs_invariant I)).toRepresentation := by
  let f := Fin.castLE hd
  have hlocal : ∀ a, ((A ∘ pairLetterMap f f) a ∧
      (label ∘ pairLetterMap f f) a = k) ↔ output a ∈ I := by
    intro a
    rw [Function.comp_apply,Function.comp_apply,he,output_pairLetterMap f (fun _ => rfl)]
  rw [standard_placed e hr hc hd]
  exact (projectedPiece ((enumerate rs).trans e) k I _ _ hlocal).lift f (fun _ => rfl) A label

def WordPacking.binaryBounded {rs ss ps : List ℕ} {μ ν : YoungDiagram} {d E : ℕ}
    (e : Cells rs ≃ μ.cells) (f : Cells ss ≃ ν.cells)
    (hr : ∀ c, (e c).val.1 = row c)
    (hc : ∀ c c', (e c).val.2 = (e c').val.2 ↔ col c = col c')
    (hr' : ∀ c, (f c).val.1 = row c)
    (hc' : ∀ c c', (f c).val.2 = (f c').val.2 ↔ col c = col c')
    (hd : μ.colLen 0 ≤ d) (hd' : ν.colLen 0 ≤ d)
    (hsum : ps.sum = (rs++ss).sum) (hlen : ps.length ≤ E)
    (k l : ℕ) (hne : k ≠ l) (I J : Set ℕ)
    (A : Fin (d*d) → Prop) (label : Fin (d*d) → ℕ)
    (he : ∀ a, (A a ∧ label a = k) ↔ output a ∈ I)
    (he' : ∀ a, (A a ∧ label a = l) ↔ output a ∈ J)
    (hs : SupportLE (wordRep (rs++ss).sum E)
      (Representation.coind (sumPermHom (appendPositions rs ss))
        (outer (projectedSpechtTensor ((enumerate rs).trans e) ((enumerate rs).trans e)
          (inOutputs I) (inOutputs_invariant I)).toRepresentation
          (projectedSpechtTensor ((enumerate ss).trans f) ((enumerate ss).trans f)
            (inOutputs J) (inOutputs_invariant J)).toRepresentation))) :
    WordPacking (rs++ss) ps d A label {k,l} := by
  classical
  let W := projectedSpechtTensor ((enumerate rs).trans e) ((enumerate rs).trans e)
    (inOutputs I) (inOutputs_invariant I)
  let X := projectedSpechtTensor ((enumerate ss).trans f) ((enumerate ss).trans f)
    (inOutputs J) (inOutputs_invariant J)
  letI : AddCommGroup (W.toSubmodule ⊗[ℂ] X.toSubmodule) := Module.addCommMonoidToAddCommGroup ℂ
  let P := placedPiece e hr hc hd k I A label he
  let Q := placedPiece f hr' hc' hd' l J A label he'
  let w := Classical.choose (exists_word_of_parts ps hsum)
  have hw := Classical.choose_spec (exists_word_of_parts ps hsum)
  let R := P.join Q (appendPositions rs ss) (fun _ _ => hne)
  have ht : SupportLE (cyclic (wordRep (rs++ss).sum ps.length) (Pi.single w 1)).toRepresentation
      (wordRep (rs++ss).sum E) :=
    (SupportLE.of_injective (subrepInclusion (cyclic (wordRep (rs++ss).sum _) (Pi.single w 1)))
      Subtype.val_injective).trans (SupportLE.of_injective (letterLift (Fin.castLE hlen))
        (letterLift_injective _ (Fin.castLE_injective hlen)))
  refine {
    word := w
    counts := hw
    packing := {
      G := Equiv.Perm (Fin rs.sum) × Equiv.Perm (Fin ss.sum)
      Y := W.toSubmodule ⊗[ℂ] X.toSubmodule
      c := joinedLabels (appendPositions rs ss) (fun _ => k) (fun _ => l)
      σ := columnOutputSums ((enumerate rs).trans e) (fun _ => k) +
        columnOutputSums ((enumerate ss).trans f) (fun _ => l)
      φ := (joinedFiberHom (appendPositions rs ss) (fun _ => k) (fun _ => l)).comp
        ((singleFiberHom rs.sum k).prodMap (singleFiberHom ss.sum l))
      τ := outer W.toRepresentation X.toRepresentation
      piece := ?_
      support := ht.trans hs }
    marksBound := ?_ }
  · rw [blocks_append]
    exact R
  · intro i
    change joinedLabels (appendPositions rs ss) (fun _ => k) (fun _ => l) i ∈ ({k,l} : Finset ℕ)
    unfold joinedLabels
    cases appendPositions rs ss i <;> simp

end Saxl.Balance
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Band_TwoPathGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two Path Geometry. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl.Balance

def appendShortTableau {n a b : ℕ} (p r q : ℕ) (hq : p+r=q)
    (e : Fin n ≃ Fin a ⊕ Fin b)
    (s : Tableau a (ShortColumns.shape p 1))
    (t : Tableau b (ShortColumns.shape r 1)) : Tableau n (ShortColumns.shape q 2) :=
  e.trans ((s.sumCongr t).trans (appendShortCells p r q hq))

def twoPathLeft {n : ℕ} (p r q : ℕ) (hq : p+r=q)
    (e : Fin n ≃ Fin (2*p+1) ⊕ Fin (2*r+1)) :
    Tableau n (ShortColumns.shape q 2) :=
  appendShortTableau p r q hq e (neighborLayer p) (neighborLayer r)

def twoPathRight {n : ℕ} (p r q : ℕ) (hq : p+r=q)
    (e : Fin n ≃ Fin (2*p+1) ⊕ Fin (2*r+1)) :
    Tableau n (ShortColumns.shape q 2) :=
  appendShortTableau r p q (by omega) (e.trans (Equiv.sumComm _ _))
    (Fin.revPerm.trans (neighborLayer r)) (Fin.revPerm.trans (neighborLayer p))

end Saxl.Balance
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Band_RunBands
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Run Bands. -/

section

noncomputable section
namespace Saxl.Balance

def runBands (a m q U : ℕ) (hg : a+2*m ≤ q) (hU : q ≤ U) : OutputBands where
  starts := Finset.range a ∪ pairMarks a m ∪ {q}
  upper k := if k = q then U else if k ∈ pairMarks a m then k+1 else k
  nonempty := by
    intro k hk
    split_ifs with h h
    · omega
    · omega
    · omega
  separated := by
    intro k hk l hl hkl
    have hk' : k < a ∨ k ∈ pairMarks a m ∨ k = q := by
      simpa only [Finset.mem_union,Finset.mem_range,Finset.mem_singleton,or_assoc] using hk
    have hl' : l < a ∨ l ∈ pairMarks a m ∨ l = q := by
      simpa only [Finset.mem_union,Finset.mem_range,Finset.mem_singleton,or_assoc] using hl
    have hle : l ≤ q := by
      rcases hl' with h | h | h
      · omega
      · have := pairMarks_bound h; omega
      · omega
    rw [ite_eq_right (by omega)]
    split_ifs with hm
    · have hb := pairMarks_bound hm
      rcases hl' with h | h | h
      · omega
      · exact pairMarks_separated hm h hkl
      · omega
    · exact hkl

end Saxl.Balance
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Balance_BalanceAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Balance Assembly. -/

section

noncomputable section
namespace Saxl.Balance
open FlagColumns Columns

def balanceColumns (M b δ τ ε m : ℕ) : List ℕ :=
  ((bigColumns (M-1+b) δ ++ shortColumns (b+1) τ) ++
    pairColumns (3+τ+ε) m) ++ oneIf (3+τ) ε

end Saxl.Balance
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_ColumnRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Column Restriction. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl.FlagColumns
open Columns

def placedFlagMap {rs : List ℕ} {μ : YoungDiagram} {d : ℕ}
    (e : Cells rs ≃ μ.cells) (N : ℕ → Fin d → ℂ) :
    Representation.IntertwiningMap (spechtRep ((enumerate rs).trans e))
      (wordRep rs.sum d) :=
  (wordMap (fun i : Fin (μ.colLen 0) => N i.val)).comp
    (subrepInclusion (spechtSub ((enumerate rs).trans e)))

end Saxl.FlagColumns
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_NoMixedColumns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! No Mixed Columns. -/

section

noncomputable section
namespace Saxl.FlagColumns
open Columns

def clearSlots {D : ℕ} (P : Fin D → Prop) :
    (ps : List (ℕ × ℕ)) → (Fin (ps.map (fun p => p.1+p.2)).sum → Fin D) → Prop
  | [], _ => True
  | (a,b)::ps, w =>
      (b ≠ 0 → ∀ i : Fin a,
        P ((leftWord finSumFinEquiv.symm w) (Fin.castAdd b i))) ∧
      clearSlots P ps (rightWord finSumFinEquiv.symm w)

end Saxl.FlagColumns
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Capacity_NumericBands
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numeric Bands. -/

section

noncomputable section
namespace Saxl.Balance

instance instDecidableBandsValid (es : List (ℕ × ℕ)) : Decidable (BandsValid es) := by
  unfold BandsValid
  infer_instance

lemma bandUpper_eq {es : List (ℕ × ℕ)} (h : BandsValid es) {e : ℕ × ℕ}
    (he : e ∈ es) : bandUpper es e.1 = e.2 := by
  apply le_antisymm
  · apply Finset.sup_le
    intro f hf
    by_cases hf' : f.1 = e.1
    · simp only [ite_eq_left hf']
      exact ((h.2 f (List.mem_toFinset.mp hf) e he).1 hf').le
    · simp only [ite_eq_right hf']; exact Nat.zero_le _
  · have hh := Finset.le_sup (f := fun f : ℕ × ℕ => if f.1 = e.1 then f.2 else 0)
      (List.mem_toFinset.mpr he)
    simpa only [bandUpper, ite_true, if_true] using hh

def numericBands (es : List (ℕ × ℕ)) (h : BandsValid es) : OutputBands where
  starts := bandStarts es
  upper := bandUpper es
  nonempty := by
    intro k hk
    obtain ⟨e,he,rfl⟩ := mem_bandStarts.mp hk
    rw [bandUpper_eq h he]
    exact h.1 e he
  separated := by
    intro k hk l hl hkl
    obtain ⟨e,he,rfl⟩ := mem_bandStarts.mp hk
    obtain ⟨f,hf,rfl⟩ := mem_bandStarts.mp hl
    rw [bandUpper_eq h he]
    exact (h.2 e he f hf).2 hkl

end Saxl.Balance
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Tensor. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

namespace FlagColumns
open Columns

def standardTableau (rs : List ℕ) : Tableau rs.sum (columnShape rs) :=
  (standard_exists_tableau rs).choose

def positioned {n d : ℕ} (rs : List ℕ) (e : Fin n ≃ Fin rs.sum)
    (N : ℕ → Fin d → ℂ) : WordSpace n d := relabelWord e.symm (blocks rs N)

end FlagColumns
end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_YoungConverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Young Converse. -/

section

noncomputable section
namespace Saxl
open scoped BigOperators

lemma rowPrefix_eq_count {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) (k : ℕ) :
    rowPrefix μ k = (Finset.univ.filter (fun i => (t i).val.1 < k)).card := by
  classical
  rw [← rowTruncate_card]
  change (μ.cells.filter (fun c => c.1 < k)).card = _
  conv_lhs => rw [← tableau_image t]
  rw [Finset.filter_image, Finset.card_image_iff.mpr]
  intro i hi j hj h
  exact t.injective (Subtype.val_injective h)

lemma rowPrefix_eq_sum_indicator {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) (k : ℕ) :
    (rowPrefix μ k : ℤ) = ∑ i, if (t i).val.1 < k then (1 : ℤ) else 0 := by
  classical
  simp only [rowPrefix_eq_count t k, Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero]

theorem dominates_of_mixed {n : ℕ} {μ ν : YoungDiagram}
    (t : Tableau n μ) (u : Tableau n ν) (g : Equiv.Perm (Fin n))
    (hi : Function.Injective (fun i => ((u (g i)).val.1, (t i).val.2))) :
    Dominates μ ν := by
  classical
  intro k
  let f : Fin n → ℕ × ℕ := fun i => ((u (g i)).val.1, (t i).val.2)
  let w : ℕ × ℕ → ℤ := fun c => (if c.1 < k then 1 else 0) -
    (if μ.colLen c.2 < k then 1 else 0)
  have h := finset_signed_sum_le (Finset.univ.image f) μ.cells w
    (fun c hc => by
      have hh := YoungDiagram.mem_iff_lt_colLen.mp hc
      dsimp only [w]
      split_ifs <;> omega)
    (fun c hc => by
      have hh : μ.colLen c.2 ≤ c.1 :=
        le_of_not_gt (fun h => hc (YoungDiagram.mem_iff_lt_colLen.mpr h))
      dsimp only [w]
      split_ifs <;> omega)
  rw [Finset.sum_image (fun _ _ _ _ h => hi h), ← tableau_sum t w] at h
  simp only [w, Finset.sum_sub_distrib] at h
  rw [Equiv.sum_comp g (fun i => if (u i).val.1 < k then (1 : ℤ) else 0),
    ← rowPrefix_eq_sum_indicator u k, ← rowPrefix_eq_sum_indicator t k] at h
  have hh : (rowPrefix ν k : ℤ) ≤ rowPrefix μ k := by omega
  exact_mod_cast hh

theorem dominates_of_tabloid_hom {n : ℕ} {μ ν : YoungDiagram}
    (t : Tableau n μ) (u : Tableau n ν)
    (f : Representation.IntertwiningMap (spechtRep t) (tabloidSub u).toRepresentation)
    (hf : f ≠ 0) : Dominates μ ν := by
  let := specht_irreducible t
  have hi := (Representation.IsIrreducible.injective_or_eq_zero f).resolve_right hf
  let p : Specht t := ⟨polytabloid t, mem_cyclic _ _⟩
  have hz : columnAlt t (f p).val ≠ 0 := by
    intro hz
    have he := columnOperator_intertwining t f p
    have hy : columnOperator t (tabloidSub u).toRepresentation (f p) = 0 := by
      apply Subtype.ext
      exact (columnOperator_subtype t (tabloidSub u) (f p)).trans hz
    rw [hy] at he
    have ht : columnOperator t (spechtRep t) p = 0 := hi (he.trans (map_zero f).symm)
    exact columnAlt_polytabloid_ne_zero t
      ((columnOperator_subtype t (spechtSub t) p).symm.trans (congrArg Subtype.val ht))
  obtain ⟨g,hg⟩ := mixed_injective_of_columnAlt_ne_zero t u (f p).property hz
  exact dominates_of_mixed t u g hg

theorem tabloid_supportLE {n : ℕ} {θ : YoungDiagram} (u : Tableau n θ)
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Equiv.Perm (Fin n)) V)
    (h : ∀ (μ : YoungDiagram) (t : Tableau n μ), Dominates μ θ →
      ∃ f : Representation.IntertwiningMap (spechtRep t) σ, f ≠ 0) :
    SupportLE (tabloidSub u).toRepresentation σ := by
  apply intertwining_separates_of_simple_support
  intro S hS
  let := hS
  let : AddCommGroup S.toSubmodule := Module.addCommMonoidToAddCommGroup ℂ
  obtain ⟨p, ⟨e⟩⟩ := irreducible_equiv_specht S.toRepresentation
  let t := partitionTableau p
  let i : Representation.IntertwiningMap (spechtRep t) (tabloidSub u).toRepresentation :=
    (subrepInclusion S).comp e.symm.toIntertwiningMap
  have hi : i ≠ 0 := by
    intro he
    have hz := congrArg (fun F : Representation.IntertwiningMap (spechtRep t)
      (tabloidSub u).toRepresentation => F ⟨polytabloid t, mem_cyclic _ _⟩) he
    have h0 : e.symm ⟨polytabloid t, mem_cyclic _ _⟩ = 0 := Subtype.ext hz
    have h1 := e.symm.injective (h0.trans e.symm.toLinearEquiv.map_zero.symm)
    exact polytabloid_ne_zero t (congrArg Subtype.val h1)
  obtain ⟨f,hf⟩ := h _ t (dominates_of_tabloid_hom t u i hi)
  refine ⟨f.comp e.toIntertwiningMap, ?_⟩
  intro he
  apply hf
  ext y
  obtain ⟨z,rfl⟩ := e.surjective y
  exact congrArg (fun F : Representation.IntertwiningMap S.toRepresentation σ => F z) he

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_CountedPieri
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Counted Pieri. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

def orbitTensorEval {b k : ℕ} {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
    (c : Fin b → Fin k) :
    Y ⊗[ℂ] (cyclic (wordRep b k) (Pi.single c 1)).toSubmodule →ₗ[ℂ]
      ((Fin b → Fin k) → Y) :=
  (TensorProduct.piScalarRight ℂ ℂ Y (Fin b → Fin k)).toLinearMap.comp
    (TensorProduct.map LinearMap.id
      (subrepInclusion (cyclic (wordRep b k) (Pi.single c 1))).toLinearMap)

@[simp] lemma orbitTensorEval_tmul {b k : ℕ} {Y : Type*}
    [AddCommGroup Y] [Module ℂ Y] (c : Fin b → Fin k) (y : Y)
    (z : (cyclic (wordRep b k) (Pi.single c 1)).toSubmodule) (w : Fin b → Fin k) :
    orbitTensorEval c (y ⊗ₜ[ℂ] z) w = z.val w • y := by
  simp only [orbitTensorEval,LinearMap.comp_apply,TensorProduct.map_tmul,
    LinearMap.id_apply]
  rfl

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_CountedGluing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Counted Gluing. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

lemma single_coindLift_injective {n : ℕ} {Y : Type*}
    [AddCommGroup Y] [Module ℂ Y]
    (σ : Representation ℂ (Equiv.Perm (Fin n)) Y) (k : ℕ) :
    Function.Injective (coindLift
      ((fiberGroup (fun _ : Fin n => k)).subtype.comp (Balance.singleFiberHom n k))
      (Representation.IntertwiningMap.id σ)) := by
  intro x y he
  have hh := congrArg (fun z => z.val 1) he
  change σ 1 x = σ 1 y at hh
  simpa only [map_one,Module.End.one_apply] using hh

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Balance_WordPackingCone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Word Packing Cone. -/

section

noncomputable section
namespace Saxl.Balance
open FlagColumns Columns

def WordPacking.cone {rs : List ℕ} {μ θ : YoungDiagram} {d : ℕ}
    (e : Cells rs ≃ μ.cells)
    (hr : ∀ c, (e c).val.1 = row c)
    (hc : ∀ c c', (e c).val.2 = (e c').val.2 ↔ col c = col c')
    (hD : μ.colLen 0 ≤ d) (ht : θ.card = rs.sum)
    (k : ℕ) (I : Set ℕ) (A : Fin (d*d) → Prop) (label : Fin (d*d) → ℕ)
    (he : ∀ a, (A a ∧ label a = k) ↔ output a ∈ I)
    (hs : ∀ (ν : YoungDiagram) (t : Tableau rs.sum ν), Dominates ν θ →
      ∃ F : Representation.IntertwiningMap (spechtRep t)
        (projectedSpechtTensor ((enumerate rs).trans e) ((enumerate rs).trans e)
          (inOutputs I) (inOutputs_invariant I)).toRepresentation, F ≠ 0) :
    WordPacking rs θ.rowLens d A label {k} := by
  classical
  let W := projectedSpechtTensor ((enumerate rs).trans e) ((enumerate rs).trans e)
    (inOutputs I) (inOutputs_invariant I)
  let φ := (fiberGroup (fun _ : Fin rs.sum => k)).subtype.comp (singleFiberHom rs.sum k)
  letI : AddCommGroup (Representation.coindV φ W.toRepresentation) := Module.addCommMonoidToAddCommGroup ℂ
  let u := canonicalTableau θ ht
  let q : Fin (θ.colLen 0) ≃ Fin θ.rowLens.length := finCongr YoungDiagram.length_rowLens.symm
  let w := q ∘ rowWord u
  let P := placedPiece e hr hc hD k I A label he
  have hh : SupportLE (tabloidSub u).toRepresentation (Representation.coind φ W.toRepresentation) :=
    (tabloid_supportLE u W.toRepresentation hs).trans
      (SupportLE.of_injective _ (single_coindLift_injective W.toRepresentation k))
  change SupportLE (cyclic (wordRep rs.sum (θ.colLen 0))
    (Pi.single (rowWord u) 1)).toRepresentation (Representation.coind φ W.toRepresentation) at hh
  have hi : SupportLE
      (cyclic (wordRep rs.sum θ.rowLens.length) ((letterLift q) (Pi.single (rowWord u) 1))).toRepresentation
      (Representation.coind φ W.toRepresentation) := by
    apply SupportLE.cyclic_image (Pi.single (rowWord u) 1) (letterLift q)
    exact hh
  rw [letterLift_single] at hi
  refine {
    word := w
    counts := ?_
    packing := {
      G := Equiv.Perm (Fin rs.sum)
      Y := W.toSubmodule
      c := fun _ => k
      σ := columnOutputSums ((enumerate rs).trans e) (fun _ => k)
      φ := singleFiberHom rs.sum k
      τ := W.toRepresentation
      piece := P
      support := hi }
    marksBound := fun _ => Finset.mem_singleton_self k }
  intro j
  rw [wordContent_lift_equiv]
  change (Finset.univ.filter (fun i => rowWord u i = q.symm j)).card = θ.rowLens.get j
  rw [rowWord_content]
  exact YoungDiagram.get_rowLens.symm

end Saxl.Balance
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_ThreeRowPieri
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Three Row Pieri. -/

section

noncomputable section
namespace Saxl

namespace ThreeRow

def colorTensor {n r a m s : ℕ} (q : Fin a ≃ Fin m ⊕ Fin m)
    (p : Fin r ≃ Fin a ⊕ Fin s) (e : Fin n ≃ Fin r ⊕ Fin 3) : WordSpace n 5 :=
  positionProduct e
    (positionProduct p (letterLift (Fin.castAdd 2) (symmetricPairs q 3))
      (Pi.single (fun _ => (3 : Fin 5)) 1))
    (Pi.single (fun _ => (4 : Fin 5)) 1)

end ThreeRow
end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_ThreeRowTensors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Three Row Tensors. -/

section

noncomputable section
namespace Saxl.ThreeRow

def powerVector (n : ℕ) {d : ℕ} (x : Fin d → ℂ) : WordSpace n d :=
  fun w => ∏ i, x (w i)

def independentTensor {n r a m s : ℕ} (q : Fin a ≃ Fin m ⊕ Fin m)
    (p : Fin r ≃ Fin a ⊕ Fin s) (e : Fin n ≃ Fin r ⊕ Fin 3)
    (Q : Matrix (Fin 3) (Fin 3) ℂ) (x y : Fin 3 → ℂ) : WordSpace n 3 :=
  positionProduct e (positionProduct p (pairFormTensor q Q) (powerVector s x))
    (powerVector 3 y)

def independentFamily {n r a m s : ℕ} (q : Fin a ≃ Fin m ⊕ Fin m)
    (p : Fin r ≃ Fin a ⊕ Fin s) (e : Fin n ≃ Fin r ⊕ Fin 3)
    (w : Coordinates) : WordSpace n 3 :=
  independentTensor q p e (matrixCoord w) (xCoord w) (yCoord w)

end Saxl.ThreeRow
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_ThreeRowGenerator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Three Row Generator. -/

section

noncomputable section
namespace Saxl.ThreeRow

def symmetricTriple : WordSpace 3 6 :=
  ∑ g : Equiv.Perm (Fin 3), Pi.single (tripleColors ∘ g) 1

def generator {n r a m s : ℕ} (q : Fin a ≃ Fin m ⊕ Fin m)
    (p : Fin r ≃ Fin a ⊕ Fin s) (e : Fin n ≃ Fin r ⊕ Fin 3) : WordSpace n 6 :=
  positionProduct e (positionProduct p (pairFormTensor q sixPairForm)
    (Pi.single (fun _ => (0 : Fin 6)) 1)) symmetricTriple

end Saxl.ThreeRow
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_ThreeRowColumns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Three Row Columns. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl.ThreeRow
open FlagColumns Columns Balance

def sixSquare {n : ℕ} (v : WordSpace n 3) : WordSpace n 6 :=
  restrictLetters pairLetters (wordTensor n 3 3 (v ⊗ₜ[ℂ] v))

end Saxl.ThreeRow
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_ColumnCertificates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Column Certificates. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

namespace Columns

def signedRowWord (μ : YoungDiagram) (π : Perms μ.transpose.rowLens) :
    Fin μ.transpose.rowLens.sum → Fin (μ.colLen 0) :=
  fun q => ⟨row (perm π (enumerate μ.transpose.rowLens q)), row_lt μ _⟩

def sgInteger : {rs : List ℕ} → Perms rs → ℤ
  | [], _ => 1
  | _ :: _, (π, σ) => (Equiv.Perm.sign π : ℤ) * sgInteger σ

def tableFor {n : ℕ} (μ : YoungDiagram) (rs : List ℕ)
    (h : μ.transpose.rowLens = rs) (e : Fin n ≃ Fin rs.sum) : Tableau n μ :=
  e.trans (h ▸ columnTableau μ)

def contractionInteger {n : ℕ} (rsA rsB rsT : List ℕ)
    (ea : Fin n ≃ Fin rsA.sum) (eb : Fin n ≃ Fin rsB.sum) (et : Fin n ≃ Fin rsT.sum)
    (L : ℕ → ℕ → ℕ → ℤ) : ℤ :=
  ∑ π : Perms rsT, ∑ σ : Perms rsA, ∑ τ : Perms rsB,
    sgInteger π * sgInteger σ * sgInteger τ *
      ∏ i : Fin n, L (row (perm π (enumerate rsT (et i))))
        (row (perm σ (enumerate rsA (ea i))))
        (row (perm τ (enumerate rsB (eb i))))

end Columns
end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_DomainContractions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Domain Contractions. -/

section

open scoped BigOperators
namespace Saxl.Columns

def Domains.weight : {rs : List ℕ} → Domains rs → Perms rs → ℤ
  | [], _, _ => 1
  | _ :: _, (s,D), (π,σ) => (if π ∈ s then (Equiv.Perm.sign π : ℤ) else 0) * weight D σ

def Domains.atValue : {rs : List ℕ} → Domains rs → Cells rs → ℕ → Domains rs
  | _ :: _, (s,D), .inl i, j => (s.filter (fun π => (π i).val = j),D)
  | _ :: _, (s,D), .inr c, j => (s,atValue D c j)

abbrev Edge (rsT rsA rsB : List ℕ) := Cells rsT × Cells rsA × Cells rsB

def domainContraction {rsT rsA rsB : List ℕ}
    (D : Domains rsT) (E : Domains rsA) (F : Domains rsB)
    (edges : List (Edge rsT rsA rsB)) (flag : Finset (ℕ × ℕ × ℕ)) : ℤ :=
  ∑ π : Perms rsT, ∑ σ : Perms rsA, ∑ τ : Perms rsB,
    D.weight π * E.weight σ * F.weight τ *
      (edges.map (fun c => if (row (perm π c.1), row (perm σ c.2.1),
        row (perm τ c.2.2)) ∈ flag then (1 : ℤ) else 0)).prod

end Saxl.Columns
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_DomainSolver
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Domain Solver. -/

section

open scoped BigOperators
namespace Saxl.Columns

def edgeOptions {rsT rsA rsB : List ℕ}
    (D : Domains rsT) (E : Domains rsA) (F : Domains rsB)
    (c : Edge rsT rsA rsB) (flag : Finset (ℕ × ℕ × ℕ)) : Finset (ℕ × ℕ × ℕ) :=
  flag.filter (fun v => (D.atValue c.1 v.1).vanished = false ∧
    (E.atValue c.2.1 v.2.1).vanished = false ∧ (F.atValue c.2.2 v.2.2).vanished = false)

def orderEdges {rsT rsA rsB : List ℕ}
    (D : Domains rsT) (E : Domains rsA) (F : Domains rsB)
    (edges : List (Edge rsT rsA rsB)) (flag : Finset (ℕ × ℕ × ℕ)) : List (Edge rsT rsA rsB) :=
  bringBest (fun c => (edgeOptions D E F c flag).card) edges

def solveDomains {rsT rsA rsB : List ℕ} : ℕ → Domains rsT → Domains rsA → Domains rsB →
    List (Edge rsT rsA rsB) → Finset (ℕ × ℕ × ℕ) → ℤ
  | fuel, D, E, F, edges, flag =>
    if D.vanished || E.vanished || F.vanished then 0
    else match orderEdges D E F edges flag with
      | [] => D.mass * E.mass * F.mass
      | c :: cs => match fuel with
        | 0 => 0
        | k+1 => ∑ v ∈ edgeOptions D E F c flag,
          solveDomains k (D.atValue c.1 v.1) (E.atValue c.2.1 v.2.1)
            (F.atValue c.2.2 v.2.2) cs flag

def certificateEdges {n : ℕ} (rsA rsB rsT : List ℕ)
    (ea : Fin n ≃ Fin rsA.sum) (eb : Fin n ≃ Fin rsB.sum) (et : Fin n ≃ Fin rsT.sum) :
    List (Edge rsT rsA rsB) :=
  List.ofFn (fun i => (enumerate rsT (et i), enumerate rsA (ea i), enumerate rsB (eb i)))

end Saxl.Columns
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_CompactDomainsCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact Domains Core. -/

section

open scoped BigOperators
namespace Saxl.Columns

def CompactDomains.atValue : {rs : List ℕ} → CompactDomains rs → Cells rs → ℕ → CompactDomains rs
  | _ :: _, (s,D), .inl i, j => (s.atValue i j,D)
  | _ :: _, (s,D), .inr c, j => (s,atValue D c j)

def compactEdgeOptions {rsT rsA rsB : List ℕ}
    (D : CompactDomains rsT) (E : CompactDomains rsA) (F : CompactDomains rsB)
    (c : Edge rsT rsA rsB) (flag : Finset (ℕ × ℕ × ℕ)) : Finset (ℕ × ℕ × ℕ) :=
  flag.filter (fun v => (D.atValue c.1 v.1).vanished = false ∧
    (E.atValue c.2.1 v.2.1).vanished = false ∧ (F.atValue c.2.2 v.2.2).vanished = false)

def compactOrderEdges {rsT rsA rsB : List ℕ}
    (D : CompactDomains rsT) (E : CompactDomains rsA) (F : CompactDomains rsB)
    (edges : List (Edge rsT rsA rsB)) (flag : Finset (ℕ × ℕ × ℕ)) : List (Edge rsT rsA rsB) :=
  bringBest (fun c => (compactEdgeOptions D E F c flag).card) edges

def solveCompact {rsT rsA rsB : List ℕ} : ℕ → CompactDomains rsT → CompactDomains rsA →
    CompactDomains rsB → List (Edge rsT rsA rsB) → Finset (ℕ × ℕ × ℕ) → ℤ
  | fuel, D, E, F, edges, flag =>
    if D.vanished || E.vanished || F.vanished then 0
    else match compactOrderEdges D E F edges flag with
      | [] => D.mass * E.mass * F.mass
      | c :: cs => match fuel with
        | 0 => 0
        | k+1 => ∑ v ∈ compactEdgeOptions D E F c flag,
          solveCompact k (D.atValue c.1 v.1) (E.atValue c.2.1 v.2.1)
            (F.atValue c.2.2 v.2.2) cs flag

end Saxl.Columns

end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_FinitePieri
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Pieri. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl.Balance
open FlagColumns Columns

def WordPacking.permute {rs ps qs : List ℕ} {d : ℕ}
    {A : Fin (d*d) → Prop} {label : Fin (d*d) → ℕ} {marks : Finset ℕ}
    (P : WordPacking rs ps d A label marks) (h : ps.Perm qs) :
    WordPacking rs qs d A label marks := by
  classical
  let q := Classical.choose (list_get_equiv h)
  have hq := Classical.choose_spec (list_get_equiv h)
  refine {
    word := q ∘ P.word
    counts := ?_
    packing := (P.packing.map (letterLift q)).congr rfl (letterLift_single q P.word)
    marksBound := P.marksBound }
  intro j
  rw [wordContent_lift_equiv,P.counts,← hq,Equiv.apply_symm_apply]

end Saxl.Balance

end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_ChoiceContractions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Choice Contractions. -/

section

open scoped BigOperators
namespace Saxl.Columns

def solveChoices {rsT rsA rsB : List ℕ} : EdgeChoices → CompactDomains rsT →
    CompactDomains rsA → CompactDomains rsB → List (Edge rsT rsA rsB) →
      Finset (ℕ × ℕ × ℕ) → ℤ
  | .fallback, D, E, F, edges, flag => solveCompact edges.length D E F edges flag
  | .node i next, D, E, F, edges, flag =>
      if D.vanished || E.vanished || F.vanished then 0
      else match edges.rotate i with
        | [] => D.mass * E.mass * F.mass
        | c :: cs => ∑ v ∈ compactEdgeOptions D E F c flag,
            solveChoices (next v) (D.atValue c.1 v.1) (E.atValue c.2.1 v.2.1)
              (F.atValue c.2.2 v.2.2) cs flag

end Saxl.Columns

end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreePlans14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Plans 14. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreePlan14_0 : PackingPlan := (.join (.neighbor 4 [3,2,2,2]) (.twosOdd 2 1 [3,2]))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegionData39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Region Data 39. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeRegion39_0 : PrefixRegion := ([(1,10),(2,12)], [(1,10),(6,34)])

end UniversalTensorSquare
end
end

end OAI
end


